#include <stdlib.h>
#include <string.h>

#include "cregex.h"

/* The VM executes one or more threads, each running a regular expression
 * program, which is just a list of regular expression instructions. Each
 * thread maintains two registers while it runs: a program counter (PC) and
 * a string pointer (SP).
 */
typedef struct {
    int visited;
    const cregex_program_instr_t *pc;
    const char *matches[REGEX_VM_MAX_MATCHES];
} vm_thread;

/* Run program on string */
static int vm_run(const cregex_program_t *program,
                  const char *string,
                  const char **matches,
                  int nmatches);

/* Run program on string (using a previously allocated buffer of at least
 * vm_estimate_threads(program) threads)
 */
static int vm_run_with_threads(const cregex_program_t *program,
                               const char *string,
                               const char **matches,
                               int nmatches,
                               vm_thread *threads);

typedef struct {
    int nthreads;
    vm_thread *threads;
} vm_thread_list;

/* vm_add_thread() recurses once per epsilon transition (SPLIT/JUMP/
 * assertion/SAVE) it walks through between two consecutive "real"
 * character-consuming instructions. A long run of these with nothing in
 * between to terminate the descent early -- e.g. a quantified *empty*
 * sub-pattern such as "(){555}{55}" -- can drive recursion depth close to
 * the total instruction count of the compiled program, which is enough to
 * blow the call stack well before REGEX_PROGRAM_MAX_INSTRUCTIONS is ever
 * reached (confirmed via fuzzing: ASan stack-overflow). Cap the depth and
 * simply stop exploring that path once hit, rather than adding the
 * thread -- equivalent to the pattern failing to match along that
 * particular (pathological) branch, not a crash.
 */
#define REGEX_VM_MAX_RECURSION_DEPTH 5000

static void vm_add_thread(vm_thread_list *list,
                          const cregex_program_t *program,
                          const cregex_program_instr_t *pc,
                          const char *string,
                          const char *sp,
                          const char **matches,
                          int nmatches,
                          int depth)
{
    if (depth > REGEX_VM_MAX_RECURSION_DEPTH)
        return;

    if (list->threads[pc - program->instructions].visited == sp - string + 1)
        return;
    list->threads[pc - program->instructions].visited = (int)(sp - string + 1);

    switch (pc->opcode) {
    case REGEX_PROGRAM_OPCODE_MATCH:
        /* fall-through */

    /* Characters */
    case REGEX_PROGRAM_OPCODE_CHARACTER:
    case REGEX_PROGRAM_OPCODE_ANY_CHARACTER:
    case REGEX_PROGRAM_OPCODE_CHARACTER_CLASS:
    case REGEX_PROGRAM_OPCODE_CHARACTER_CLASS_NEGATED:
        list->threads[list->nthreads].pc = pc;
        memcpy((void*)list->threads[list->nthreads].matches, matches,
               sizeof(matches[0]) * ((nmatches <= REGEX_VM_MAX_MATCHES)
                                         ? nmatches
                                         : REGEX_VM_MAX_MATCHES));
        ++list->nthreads;
        break;

    /* Control-flow */
    case REGEX_PROGRAM_OPCODE_SPLIT:
        vm_add_thread(list, program, pc->first, string, sp, matches, nmatches, depth + 1);
        vm_add_thread(list, program, pc->second, string, sp, matches, nmatches, depth + 1);
        break;
    case REGEX_PROGRAM_OPCODE_JUMP:
        vm_add_thread(list, program, pc->target, string, sp, matches, nmatches, depth + 1);
        break;

    /* Assertions */
    case REGEX_PROGRAM_OPCODE_ASSERT_BEGIN:
        if (sp == string)
            vm_add_thread(list, program, pc + 1, string, sp, matches, nmatches, depth + 1);
        break;
    case REGEX_PROGRAM_OPCODE_ASSERT_END:
        if (!*sp)
            vm_add_thread(list, program, pc + 1, string, sp, matches, nmatches, depth + 1);
        break;

    /* Saving */
    case REGEX_PROGRAM_OPCODE_SAVE:
        if (pc->save < nmatches && pc->save < REGEX_VM_MAX_MATCHES) {
            const char *saved = matches[pc->save];
            matches[pc->save] = sp;
            vm_add_thread(list, program, pc + 1, string, sp, matches, nmatches, depth + 1);
            matches[pc->save] = saved;
        } else {
            vm_add_thread(list, program, pc + 1, string, sp, matches, nmatches, depth + 1);
        }
        break;
    }
}

/* Upper bound of number of threads required to run program */
static int vm_estimate_threads(const cregex_program_t *program)
{
    return program->ninstructions * 2;
}

static int vm_run(const cregex_program_t *program,
                  const char *string,
                  const char **matches,
                  int nmatches)
{
    size_t size = sizeof(vm_thread) * vm_estimate_threads(program);
    vm_thread *threads;
    int matched;

    if (!(threads = malloc(size)))
        return -1;

    matched = vm_run_with_threads(program, string, matches, nmatches, threads);
    free(threads);
    return matched;
}

static int vm_run_with_threads(const cregex_program_t *program,
                               const char *string,
                               const char **matches,
                               int nmatches,
                               vm_thread *threads)
{
    vm_thread_list *current =
        &(vm_thread_list){.nthreads = 0, .threads = threads};
    vm_thread_list *next = &(vm_thread_list){
        .nthreads = 0, .threads = threads + program->ninstructions};
    int matched = 0;

    memset(matches, 0, sizeof(char*) * nmatches);
    memset(threads, 0, sizeof(vm_thread) * program->ninstructions * 2);

    vm_add_thread(current, program, program->instructions, string, string,
                  matches, nmatches, 0);

    for (const char *sp = string;; ++sp) {
        for (int i = 0; i < current->nthreads; ++i) {
            vm_thread *thread = current->threads + i;
            switch (thread->pc->opcode) {
            case REGEX_PROGRAM_OPCODE_MATCH:
                matched = 1;
                current->nthreads = 0;
                memcpy(matches, thread->matches,
                       sizeof(matches[0]) * ((nmatches <= REGEX_VM_MAX_MATCHES)
                                                 ? nmatches
                                                 : REGEX_VM_MAX_MATCHES));
                continue;

            /* Characters */
            case REGEX_PROGRAM_OPCODE_CHARACTER:
                if (*sp == thread->pc->ch)
                    break;
                continue;
            case REGEX_PROGRAM_OPCODE_ANY_CHARACTER:
                if (*sp)
                    break;
                continue;
            case REGEX_PROGRAM_OPCODE_CHARACTER_CLASS:
                if (*sp && cregex_char_class_contains(thread->pc->klass, *sp))
                    break;
                continue;
            case REGEX_PROGRAM_OPCODE_CHARACTER_CLASS_NEGATED:
                /* The NUL terminator is never a "real" character to match,
                 * even for a negated class (which would otherwise treat it
                 * as "not in the class" and match it) -- doing so would let
                 * sp advance one past the end of the string on the next
                 * vm_add_thread(next, ..., sp + 1, ...) call below, and
                 * potentially keep walking further out of bounds on
                 * subsequent iterations. */
                if (*sp && !cregex_char_class_contains(thread->pc->klass, *sp))
                    break;
                continue;

            /* Control-flow */
            case REGEX_PROGRAM_OPCODE_SPLIT:
            case REGEX_PROGRAM_OPCODE_JUMP:
                /* fall-through */

            /* Assertions */
            case REGEX_PROGRAM_OPCODE_ASSERT_BEGIN:
            case REGEX_PROGRAM_OPCODE_ASSERT_END:
                /* fall-through */

            /* Saving */
            case REGEX_PROGRAM_OPCODE_SAVE:
                /* handled in vm_add_thread() */
                abort();
            }

            vm_add_thread(next, program, thread->pc + 1, string, sp + 1,
                          thread->matches, nmatches, 0);
        }

        /* swap current and next thread list */
        vm_thread_list *swap = current;
        current = next;
        next = swap;
        next->nthreads = 0;

        /* done if no more threads are running or end of string reached */
        if (current->nthreads == 0 || !*sp)
            break;
    }

    return matched;
}

int cregex_program_run(const cregex_program_t *program,
                       const char *string,
                       const char **matches,
                       int nmatches)
{
    return vm_run(program, string, matches, nmatches);
}
