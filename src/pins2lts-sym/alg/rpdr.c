#include <hre/config.h>

#ifdef __APPLE__
#define _DARWIN_C_SOURCE
#endif

#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>

#include <dm/dm.h>
#include <hre/stringindex.h>
#include <hre/user.h>
#include <lts-io/user.h>
#include <pins-lib/pins.h>
#include <pins-lib/pins-impl.h>
#include <pins-lib/pins-util.h>
#include <pins2lts-sym/alg/aux.h>
#include <pins2lts-sym/alg/rpdr.h>
#include <pins2lts-sym/aux/options.h>
#include <ltsmin-lib/ltsmin-standard.h>
#include <ltsmin-lib/ltsmin-syntax.h>
#include <ltsmin-lib/ltsmin-tl.h>
#include <mc-lib/atomics.h>
#include <mc-lib/bitvector-ll.h>
#include <util-lib/bitset.h>
#include <util-lib/dfs-stack.h>
#include <util-lib/util.h>


#ifdef HAVE_SYLVAN

#include <sylvan.h>

static vset_t g_universe;


/*
 * Frame linked list structure and operations
 */

typedef struct frame
{
    vset_t states;
    struct frame* next;
    struct frame* prev;
} frame;

void
create_new_frame(vset_t frame, vset_t universe)
{
    vset_copy(frame, universe);
}

bool
frame_is_initial(frame *f)
{
    return f->prev == NULL;
}

bool
frame_is_final(frame *f)
{
    return f->next == NULL;
}

void
insert_before(frame *list, frame *new)
{
    new->next = list;
    new->prev = list->prev;

    new->prev->next = new;
    new->next->prev = new;
}


vset_t
post(vset_t dst, vset_t source, vset_t universe)
{
    add_step(false, dst, source, universe);
}

vset_t
pre(vset_t dst, vset_t source, vset_t universe)
{
    add_step(true, dst, source, universe);
}

vset_t
reverse_reachability_counterexample(vset_t counter_examples, vset_t V, int depth)
{
    vset_t reverse_reachable = copy(counter_examples);
    vset_t current_reach = copy(counter_examples);
    vset_t new_reach = empty();
    for (int i=0; i < depth; i++) {
        add_step(true, new_reach, current_reach, V);
        vset_union(reverse_reachable, new_reach);

        vset_destroy(current_reach);

        current_reach = new_reach;
        new_reach = empty();
    }
    return reverse_reachable;
}

//bool
//refine_reachable_states(vset_t unsafe, vset_t* reachable, int depth)
//{
//    bool is_counter_example;
//
//    vset_t new_unsafe = reverse_reachability_step(unsafe, reachable[depth]);
//    if (vset_is_empty(new_unsafe)) {
//        return false;
//    }
//
//    if (depth == 0) {
//        return true;        // Real counterexample found; unsafe n I != {}
//    }
//
//    is_counter_example = refine_reachable_states(new_unsafe, reachable, depth - 1);
//
//    if (!is_counter_example) {
//        vset_minus(reachable[depth], new_unsafe);
//    }
//
//    return is_counter_example;
//}

/**
 *
 * @return a single bad state
 */
void
get_bad_states(vset_t bad_states, vset_t universe, vset_t P)
{
    vset_copy(bad_states, universe);
    vset_minus(bad_states, P);
}

bool
contains_initial(vset_t states)
{
    vset_t tmp = vset_create(domain, -1, NULL);

    vset_copy(tmp, states);
    vset_intersect(tmp, initial);

    return (bool) vset_is_empty(tmp);
}

bool
is_relative_inductive(vset_t states, frame *f)
{
    vset_t tmp = vset_create(domain, -1, NULL);

    post(tmp, f->states, states); // Post(prev(current_frame).states) /\ states

    return (bool) vset_is_empty(tmp); // == 0
}

void
generalize(vset_t states, frame *current_frame)
{
    ci_list *projection = ci_create((size_t)N); // TODO: add size of base/full projection
    ci_list *tmp_projection = ci_create((size_t)N);
    ci_list *inverse_projection = ci_create((size_t)N);

    ci_copy(projection, total_proj);

    vset_t generalized_states;
    vset_t inverse_states;
    vset_t total_generalized_states = vset_create(domain, -1, NULL);

    for (int i = 0; i < nGrps; i++) {
        ci_copy(tmp_projection, projection);
        ci_minus(tmp_projection, r_projs[i]);

        generalized_states = vset_create(domain, tmp_projection->count, tmp_projection->data);

        vset_project(generalized_states, states);

        ci_invert(inverse_projection, tmp_projection, total_proj);
        inverse_states = vset_create(domain, inverse_projection->count, inverse_projection->data);
        vset_project(inverse_states, g_universe);
        vset_join(total_generalized_states, generalized_states, inverse_states);

        if (!contains_initial(generalized_states)
            && is_relative_inductive(generalized_states, current_frame)) {
            vset_copy(states, total_generalized_states);
        }
    }
}

bool
propagate_removed_states(frame *frame)
{
    struct frame *f = frame;

    while (f->prev != NULL) {
        vset_minus(f->prev->states, f->states);
        f = f->prev;
    }
}

void
recursive_remove_states(vset_t counter_example, vset_t bad_states, frame *current_frame)
{
    if (!vset_is_empty(bad_states)) {
        if (frame_is_final(current_frame)) {
            vset_intersect(bad_states, current_frame->states);
            vset_copy(counter_example, bad_states);
            return;
        }

        vset_t new_bad_states = vset_create(domain, -1, NULL);
        pre(new_bad_states, bad_states, g_universe);

        recursive_remove_states(counter_example, new_bad_states, current_frame->prev);

        if (!vset_is_empty(counter_example)) {
            return;
        }

        vset_union(bad_states, new_bad_states);

        vset_t image = vset_create(domain, -1, NULL);
        post(image, current_frame->prev->states, g_universe);
        vset_minus(bad_states, image);
    }

    generalize(bad_states, current_frame); // not so bad after all
    vset_minus(current_frame->states, bad_states);
}


bool
pdr(vset_t I, vset_t P, vset_t universe)
{
    Warning(info, "Initialize refined reachability");
    g_universe = universe;

    frame *frame_initial = RTmallocZero (sizeof(frame));
    frame_initial->states = I;

    frame *total = RTmallocZero (sizeof(frame));
    total->states = universe;

    frame_initial->next = total;
    total->prev = frame_initial;

    frame *current_frame = frame_initial;

    vset_t bad_states = vset_create(domain, -1, NULL);
    vset_t counter_example = vset_create(domain, -1, NULL);

    while(true) {
        get_bad_states(bad_states, universe, P);
        if (!vset_is_empty(bad_states)) {
            recursive_remove_states(counter_example, bad_states, current_frame);
            if (!vset_is_empty(counter_example)) {
                return false;
            }
        } else {
            // Create new frame
            current_frame = RTmallocZero (sizeof(frame));
            current_frame->states = vset_create(domain, -1, NULL);

            insert_before(total, current_frame);

            // Propagate removed states backwards
            if (propagate_removed_states(total->prev)) {
                return true;
            }
        }
    }
}

#else

bool reach_reverse_pdr(vset_t I)
{
    Warning(info, "Couldn't find sylvan");
    return false;
}

#endif
