#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "cregex.h"

typedef struct {
    const char *sp;
    cregex_node_t *stack, *output;
} regex_parse_context;

/* Shunting-yard algorithm
 * See https://en.wikipedia.org/wiki/Shunting-yard_algorithm
 */

static inline cregex_node_t *push(regex_parse_context *context,
                                  const cregex_node_t *node)
{
    assert(context->stack <= context->output);
    *context->stack = *node;
    return context->stack++;
}

static inline cregex_node_t *drop(regex_parse_context *context)
{
    return --context->stack;
}

static inline cregex_node_t *consume(regex_parse_context *context)
{
    *--context->output = *--context->stack;
    return context->output;
}

static inline cregex_node_t *concatenate(regex_parse_context *context,
                                         const cregex_node_t *bottom)
{
    if (context->stack == bottom)
        push(context, &(cregex_node_t){.type = REGEX_NODE_TYPE_EPSILON});
    else {
        while (context->stack - 1 > bottom) {
            cregex_node_t *right = consume(context);
            cregex_node_t *left = consume(context);
            push(context,
                 &(cregex_node_t){.type = REGEX_NODE_TYPE_CONCATENATION,
                                  .left = left,
                                  .right = right});
        }
    }
    return context->stack - 1;
}

static cregex_node_t *parse_char_class(regex_parse_context *context)
{
    cregex_node_type type =
        (*context->sp == '^')
            ? (++context->sp, REGEX_NODE_TYPE_CHARACTER_CLASS_NEGATED)
            : REGEX_NODE_TYPE_CHARACTER_CLASS;
    const char *from = context->sp;

    for (;;) {
        int ch = *context->sp++;
        switch (ch) {
        case '\0':
            /* premature end of character class */
            return NULL;
        case ']':
            if (context->sp - 1 == from)
                goto CHARACTER;
            return push(context,
                        &(cregex_node_t){
                            .type = type, .from = from, .to = context->sp - 1});
        case '\\':
            ch = *context->sp++;
            if (ch == '\0')
                /* premature end of character class (dangling escape) */
                return NULL;
            /* fall-through */
        default:
        CHARACTER:
            if (*context->sp == '-' && context->sp[1] != ']') {
                /* Compare as unsigned char: ch/sp[1] may be plain (signed)
                 * char values sign-extended to negative ints for bytes
                 * >= 0x80, which would make this "empty range" check pass
                 * for a bogus range (e.g. the string's own NUL terminator
                 * appearing to be "greater than" a negative ch), letting
                 * sp advance past the end of the pattern buffer. */
                if ((unsigned char)context->sp[1] < (unsigned char)ch)
                    /* empty range in character class */
                    return NULL;
                context->sp += 2;
            }
            break;
        }
    }
}

/* Upper bound for {n,m} repeat counts. Keeps digit accumulation below
 * INT_MAX (avoiding signed integer overflow / UB while parsing) and keeps
 * nmin/nmax small enough that later arithmetic on them in
 * cregex_compile.c's count_instructions() (which multiplies nmin/nmax by
 * the quantified sub-pattern's instruction count to size the compiled
 * program buffer) can't itself overflow into an undersized allocation.
 *
 * This also bounds recursion depth: a large {n,m} is compiled into a
 * chain of that many SPLIT instructions, and the VM's vm_add_thread()
 * walks that chain *recursively* while building the initial epsilon
 * closure (once per cregex_program_run() call, not just once per
 * compile). A 65535 cap was still large enough to blow a default-size
 * thread stack (confirmed via fuzzing: "a*{,61056}" stack-overflows under
 * ASan at ~61k recursive calls); 1000 leaves a wide safety margin even on
 * the smaller (~1MB) stacks Windows GUI worker threads typically get.
 */
#define REGEX_INTERVAL_MAX 1000

static cregex_node_t *parse_interval(regex_parse_context *context)
{
    const char *from = context->sp;
    int nmin, nmax;
    int overflow = 0;

    for (nmin = 0; *context->sp >= '0' && *context->sp <= '9'; ++context->sp) {
        /* Once we've exceeded the cap, stop doing arithmetic on nmin (it's
         * already rejected below) so repeated *10 can't itself overflow
         * signed int; just keep consuming digit characters. */
        if (!overflow) {
            nmin = (nmin * 10) + (*context->sp - '0');
            overflow = (nmin > REGEX_INTERVAL_MAX);
        }
    }

    if (*context->sp == ',') {
        ++context->sp;
        if (*from != ',' && *context->sp == '}')
            nmax = -1;
        else {
            for (nmax = 0; *context->sp >= '0' && *context->sp <= '9';
                 ++context->sp) {
                if (!overflow) {
                    nmax = (nmax * 10) + (*context->sp - '0');
                    overflow = (nmax > REGEX_INTERVAL_MAX);
                }
            }
            if (*(context->sp - 1) == ',' || *context->sp != '}' ||
                nmax < nmin || overflow) {
                context->sp = from;
                return NULL;
            }
        }
    } else if (*from != '}' && *context->sp == '}') {
        nmax = nmin;
    } else {
        context->sp = from;
        return NULL;
    }

    if (overflow) {
        context->sp = from;
        return NULL;
    }

    ++context->sp;
    return push(context,
                &(cregex_node_t){
                    .type = REGEX_NODE_TYPE_QUANTIFIER,
                    .nmin = nmin,
                    .nmax = nmax,
                    .greedy = (*context->sp == '?') ? (++context->sp, 0) : 1,
                    .quantified = consume(context)});
}

static cregex_node_t *parse_context(regex_parse_context *context, int depth)
{
    cregex_node_t *bottom = context->stack;

    for (;;) {
        int ch = *context->sp++;
        switch (ch) {
        /* Characters */
        case '\\':
            ch = *context->sp++;
            if (ch == '\0')
                /* dangling escape at end of pattern: don't let a later
                 * iteration read past the NUL terminator we just consumed */
                return NULL;
            /* fall-through */
        default:
        CHARACTER:
            push(context,
                 &(cregex_node_t){.type = REGEX_NODE_TYPE_CHARACTER, .ch = ch});
            break;
        case '.':
            push(context,
                 &(cregex_node_t){.type = REGEX_NODE_TYPE_ANY_CHARACTER});
            break;
        case '[':
            if (!parse_char_class(context))
                return NULL;
            break;

        /* Composites */
        case '|': {
            cregex_node_t *left = concatenate(context, bottom), *right;
            if (!(right = parse_context(context, depth)))
                return NULL;
            if (left->type == REGEX_NODE_TYPE_EPSILON &&
                right->type == left->type) {
                drop(context);
            } else if (left->type == REGEX_NODE_TYPE_EPSILON) {
                right = consume(context);
                drop(context);
                push(context,
                     &(cregex_node_t){.type = REGEX_NODE_TYPE_QUANTIFIER,
                                      .nmin = 0,
                                      .nmax = 1,
                                      .greedy = 1,
                                      .quantified = right});
            } else if (right->type == REGEX_NODE_TYPE_EPSILON) {
                drop(context);
                left = consume(context);
                push(context,
                     &(cregex_node_t){.type = REGEX_NODE_TYPE_QUANTIFIER,
                                      .nmin = 0,
                                      .nmax = 1,
                                      .greedy = 1,
                                      .quantified = left});
            } else {
                right = consume(context);
                left = consume(context);
                push(context,
                     &(cregex_node_t){.type = REGEX_NODE_TYPE_ALTERNATION,
                                      .left = left,
                                      .right = right});
            }
            return bottom;
        }

#define QUANTIFIER(ch, min, max)                                           \
    case ch:                                                               \
        if (context->stack == bottom)                                      \
            goto CHARACTER;                                                \
        push(context,                                                      \
             &(cregex_node_t){                                             \
                 .type = REGEX_NODE_TYPE_QUANTIFIER,                       \
                 .nmin = min,                                              \
                 .nmax = max,                                              \
                 .greedy = (*context->sp == '?') ? (++context->sp, 0) : 1, \
                 .quantified = consume(context)});                         \
        break

            /* clang-format off */
        /* Quantifiers */
        QUANTIFIER('?', 0, 1);
        QUANTIFIER('*', 0, -1);
        QUANTIFIER('+', 1, -1);
            /* clang-format on */
#undef QUANTIFIER

        case '{':
            if ((context->stack == bottom) || !parse_interval(context))
                goto CHARACTER;
            break;

        /* Anchors */
        case '^':
            push(context,
                 &(cregex_node_t){.type = REGEX_NODE_TYPE_ANCHOR_BEGIN});
            break;
        case '$':
            push(context, &(cregex_node_t){.type = REGEX_NODE_TYPE_ANCHOR_END});
            break;

        /* Captures */
        case '(':
            if (!parse_context(context, depth + 1))
                return NULL;
            push(context, &(cregex_node_t){.type = REGEX_NODE_TYPE_CAPTURE,
                                           .captured = consume(context)});
            break;
        case ')':
            if (depth > 0)
                return concatenate(context, bottom);
            /* unmatched close parenthesis */
            return NULL;

        /* End of string */
        case '\0':
            if (depth == 0)
                return concatenate(context, bottom);
            /* unmatched open parenthesis */
            return NULL;
        }
    }
}

static inline int estimate_nodes(const char *pattern)
{
    /* +1 so that an empty pattern ("") still gets a non-zero allocation:
     * parse_context() always pushes at least one (EPSILON) node via
     * concatenate(), even when nothing was parsed. */
    return (int)strlen(pattern) * 2 + 1;
}

/* Parse a pattern (using a previously allocated buffer of at least
 * estimate_nodes(pattern) nodes).
 */
static cregex_node_t *parse_with_nodes(const char *pattern,
                                       cregex_node_t *nodes)
{
    regex_parse_context *context =
        &(regex_parse_context){.sp = pattern,
                               .stack = nodes,
                               .output = nodes + estimate_nodes(pattern)};
    return parse_context(context, 0);
}

cregex_node_t *cregex_parse(const char *pattern)
{
    size_t size = sizeof(cregex_node_t) * estimate_nodes(pattern);
    cregex_node_t* nodes;

    nodes = malloc(size);
    if (!nodes)
        return NULL;

    if (!parse_with_nodes(pattern, nodes)) {
        free(nodes);
        return NULL;
    }

    return nodes;
}

void cregex_parse_free(cregex_node_t *root)
{
    free(root);
}
