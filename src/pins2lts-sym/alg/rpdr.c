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
#include "aux/options.h"


#ifdef HAVE_SYLVAN

#include <sylvan.h>

static vset_t g_universe;
static vset_t g_initial;

/*
 * Frame linked list structure and operations
 */

typedef struct frame
{
    vset_t states;
    struct frame* next;
    struct frame* prev;
} frame;

static void vset_count_info(vset_t set)
{
    long count;
    long double el;
    vset_count_fn(set, &count, &el);
    Warning (info, "nodes: %ld\t\t states: %.0Lf", count, el);
}

bool
frame_is_initial(frame *f)
{
    return f->prev == NULL;
}

void
insert_before(frame *list, frame *new)
{
    new->next = list;
    new->prev = list->prev;

    new->prev->next = new;
    new->next->prev = new;
}

/**
 * Calculates the image of a set
 */
vset_t
post(vset_t dst, vset_t source, vset_t universe)
{
    add_step(false, dst, source, universe);
}

/**
 * Calculates the pre-image of a set.
 */
vset_t
pre(vset_t dst, vset_t source, vset_t universe)
{
    add_step(true, dst, source, universe);
}

/**
 * Takes all states in U that do not satisfy P
 * @return a set of bad states
 */
void
get_bad_states(vset_t bad_states, vset_t universe, vset_t P)
{
    vset_copy(bad_states, universe);
    vset_minus(bad_states, P);
}

/**
 * Check if a set os states contains an initial state
 */
bool
contains_initial(vset_t states)
{
    vset_t tmp = vset_create(domain, -1, NULL);

    vset_copy(tmp, states);
    vset_intersect(tmp, g_initial);

    return vset_is_empty(tmp) >= 0;
}

/**
 * Checks relative-inductiveness of states to frame f.
 * This means that Post(states) /\ f->states = 0
 */
bool
is_relative_inductive(vset_t states, frame *f)
{
    vset_t tmp = vset_create(domain, -1, NULL);

    post(tmp, f->states, states); // Post(prev(current_frame).states) /\ states

    return (bool) vset_is_empty(tmp); // == 0
}

/**
 * Generalizes relative-inductive states to remove a bigger chunk of the state-space.
 * First a full projection is created, then for each group the values from the read projection are removed
 * from the full projection. We then check if the states are still relative-inductive to the current frame.
 * If this is still the case then the values stay removed from the projection and we go to the next group.
 * To check for relative-inductiveness we take all states in U that match states in all values for the projection.
 *
 * @param states - states that are relative inductive to the current frame
 * @param current_frame
 */
void
generalize(vset_t states, frame *current_frame)
{
    ci_list *projection = ci_create((size_t)N); // TODO: add size of base/full projection
    ci_list *tmp_projection = ci_create((size_t)N);

    ci_copy(projection, total_proj);

    vset_t generalized_states = vset_create(domain, -1, NULL);
    vset_t total_generalized_states = vset_create(domain, -1, NULL);

    for (int i = 0; i < nGrps; i++) {
        ci_copy(tmp_projection, projection);
        ci_minus(tmp_projection, r_projs[i]);

        // Compute generalized states s.t. G = U /\ proj(S)
        vset_copy_match_set(generalized_states, g_universe, states, tmp_projection->count, tmp_projection->data);

        if (!contains_initial(generalized_states)
            && is_relative_inductive(generalized_states, current_frame)) {
            vset_copy(states, total_generalized_states);
        }
    }

    ci_free(projection);
    ci_free(tmp_projection);
}

vset_t invariant_states;

/**
 * Propagate all removed states backwards and checks whether an invariant is found.
 * Each iteration we remove all states that are in prev(f) and not in f from prev(f)
 * then set f := prev(f).
 * @param frame - final frame containing the universe
 * @return true <=> an invariant is found.
 */
bool
propagate_removed_states(frame *frame)
{
    struct frame *f = frame;

    while (f->prev != NULL) {
        if (vset_equal(f->prev->states, f->states)) {
            invariant_states = vset_create(domain, -1, NULL);
            vset_copy(invariant_states, f->states);
            return true;
        }
        vset_intersect(f->prev->states, f->states);
        f = f->prev;
    }
}

/**
 * A recursive DFS algorithm that removes states that are relative inductive for each frame.
 *  First the function checks whether bad_states contains any states. If not this frame is relative
 *  inductive to the next frame.
 *  If it is not relative inductive then we check if the current frame is the initial frame:
 *      - if yes, a counter example has been found
 *  Otherwise we compute the pre-image of the bad states in this frame and execute another recursive step
 *  for the preceding frame.
 *  If no counter-examples are found in any of the preceding frames then we get states that were found to
 *  be relative inductive by the preceding frame.
 *  These states are added to the bad states of this frame (which at this point are known to not reach I).
 *  We then take the states that are (still) relative inductive.
 *  Finally all relative inductive states are generalized and removed from this frame and returned to the next
 *  frame.
 *
 * @param counter_example - set passed by reference used to return counter examples.
 * @param bad_states - states that can reach states not in P.
 * @param current_frame - current working frame with related set of states.
 */
void
recursive_remove_states(vset_t counter_example, vset_t bad_states, frame *current_frame)
{
    if (!vset_is_empty(bad_states)) {
        if (frame_is_initial(current_frame)) {
            vset_intersect(bad_states, current_frame->states);
            vset_copy(counter_example, bad_states);
            return;
        }

        vset_t new_bad_states = vset_create(domain, -1, NULL);
        pre(new_bad_states, bad_states, g_universe);

        recursive_remove_states(counter_example, new_bad_states, current_frame->prev);

        if (!vset_is_empty(counter_example)) {
            Warning(info, "Intersection with initial states");
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

/**
 * Main PDR loop:
 *  First the initial and final frames are created containing the initial states and universe.
 *  This also builds the initial (doubly) linked list structure used for the frames.
 *  Each iteration of the main loop:
 *     - Bad states are exracted from the universe.
 *     - These states are used to recursively execute a kind of backwards DFS, until
 *       a frame is reached that is relative inductive, states are removed propagating forward.
 *       If the initial states are reached a counter example is found and PDR returns false.
 *     - Next a new frame is added before the last frame.
 *     - Finally removed states are propagated backwards to make sure every frame is a subset
 *       of the next frame.
 *
 * @param I - initial states used for reachability.
 * @param P - set of states that satisfies the property.
 * @param universe - set of all states found by compositional reachability.
 * @return true <=> an invariant is found, false <=> a counter-example is found.
 */
bool
pdr(vset_t I, vset_t P, vset_t universe)
{
    Warning(info, "Initialize PDR");
    g_universe = universe;
    g_initial = I;

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
        }

        // Create new frame
        current_frame = RTmallocZero (sizeof(frame));
        current_frame->states = vset_create(domain, -1, NULL);

        insert_before(total, current_frame);

        // Propagate removed states backwards
        if (propagate_removed_states(total->prev)) {
            // All code beyond this is just verifying the invariant
            Warning(info, "Verifying invariant: ");

            vset_t inv = vset_create(domain, -1, NULL);
            Warning(info, "Checking inductiveness...");
            post(inv, invariant_states, universe);
            vset_minus(inv, invariant_states);

            Warning(info, "Checking soundness...");
            vset_minus(invariant_states, P);

            if (vset_is_empty(inv) && vset_is_empty(invariant_states)) {
                Warning(info, "invariant found");
                return true;
            } else {
                Warning(info, "error");
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
