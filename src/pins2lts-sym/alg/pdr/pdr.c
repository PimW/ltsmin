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
#include <alg/pdr/pdr.h>
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
#include "pdr-util.h"
#include "frame.h"


#ifdef HAVE_SYLVAN

#include <sylvan.h>

static vset_t g_universe;
static vset_t g_initial;

static vset_t source_states;
static vset_t goal_states;

vset_t invariant_states;

bool using_reverse_pdr;

bool
get_bad_state(int *state, vset_t source_states, vset_t seen)
{
    vset_t unseen_states = empty();

    vset_copy(unseen_states, source_states);
    vset_minus(unseen_states, seen);

    if (!vset_is_empty(unseen_states)) {
        vset_example(unseen_states, state);
        return true;
    }

    vset_destroy(unseen_states);
    return false;
}

/**
 * Check if a set os states contains an initial state
 */
bool
contains_goal(vset_t states)
{
    vset_t tmp = empty();

    vset_copy(tmp, states);
    vset_intersect(tmp, goal_states);

    bool result = (bool) vset_is_empty(tmp);

    vset_destroy(tmp);

    return !result;
}

/**
 * Checks relative-inductiveness of states to frame f.
 * This means that Post(states) /\ f->states = 0
 */
bool
is_relative_inductive(vset_t states, struct frame *f)
{
    vset_t tmp = empty();

    //post(tmp, f->prev->states, states); // Post(prev(current_frame).states) /\ states
    if (using_reverse_pdr) {
        //post(tmp, states, f->prev->states);
        pre(tmp, f->prev->states, states);
    } else {
        post(tmp, f->prev->states, states); // Post(prev(current_frame).states) /\ states
    }

    bool val =  (bool) vset_is_empty(tmp); // == 0
    vset_destroy(tmp);
    return val;
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
generalize(vset_t result_states, int* state, struct frame *current_frame)
{
    ci_list *projection = ci_create((size_t)total_proj->count); // TODO: add size of base/full projection
    ci_list *tmp_projection = ci_create((size_t)total_proj->count);

    vset_clear(result_states);
    vset_add(result_states, state);

    ci_copy(projection, total_proj);

    vset_t generalized_states = empty();

    assert(!contains_goal(result_states));
    assert(is_relative_inductive(result_states, current_frame));

    for (int i = 0; i < N; i++) {
        ci_copy(tmp_projection, projection);
        ci_remove(tmp_projection, ci_binary_search(tmp_projection, i));

        // Project the bad state to a state defined only on the vars in the projection
        int *projected_state = malloc(sizeof(int) * tmp_projection->count);
        ci_project(projected_state, state, tmp_projection);

        assert(!vset_is_empty(result_states));

        vset_copy_match(generalized_states, g_universe, tmp_projection->count, tmp_projection->data, projected_state);
        assert(!vset_is_empty(generalized_states));

        if (!contains_goal(generalized_states)
            && is_relative_inductive(generalized_states, current_frame)) {
            ci_copy(projection, tmp_projection);
            vset_copy(result_states, generalized_states);
        }
    }

    vset_destroy(generalized_states);

    ci_free(projection);
    ci_free(tmp_projection);
}



/**
 * Propagate all removed states backwards and checks whether an invariant is found.
 * Each iteration we remove all states that are in prev(f) and not in f from prev(f)
 * then set f := prev(f).
 * @param frame - final frame containing the universe
 * @return true <=> an invariant is found.
 */
bool
propagate_removed_states(struct frame *frame)
{
    struct frame *f = frame;

    int i = 0;
    while (f->prev != NULL) {
        vset_intersect(f->prev->states, f->states);
        if (vset_equal(f->prev->states, f->states)) {
            Warning(info, "propagate_removed_states: found invariant")
            invariant_states = empty();
            vset_copy(invariant_states, f->states);
            return true;
        }
        f = f->prev;
        i++;
    }
    return false;
}

void
compute_frame_sizes(struct frame *frame)
{
    struct frame *f = frame;
    long node_count = 0;

    int i = 0;
    while (f->prev != NULL) {
        if (log_active(info)) {
            vset_node_count(&node_count,frame->states);
            if (node_count > max_node_count) {
                max_node_count = node_count;
            }
        }

        f = f->prev;
        i++;
    }
}

void compute_next_states(frame *current_frame, vset_t new_bad_states, vset_t state_set) {
    if (using_reverse_pdr) {
        post(new_bad_states, state_set, current_frame->prev->states);
    } else {
        pre(new_bad_states, state_set, current_frame->prev->states);
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
    vset_t propagated_states = empty();
    vset_t new_bad_states = empty();
    vset_t state_set = empty();
    int* state = malloc(sizeof(int) * N);

    vset_t unvisited_states = empty();
    vset_copy(unvisited_states, bad_states);

    // Clear bad states and use it as the return set for forward propagation
    vset_clear(bad_states);

    if (frame_is_initial(current_frame)) {
        Warning(info, "[recursive_remove_states] Recursive remove states: reached initial frame..");
        vset_intersect(unvisited_states, current_frame->states);
        vset_copy(counter_example, unvisited_states);
        return;
    }

    while (!vset_is_empty(unvisited_states)) {
        // extract single bad state
        vset_example(unvisited_states, state);
        vset_add(state_set, state);

        // Compute (pre-)image for the bad state and intersect it with the previous frame
        vset_clear(new_bad_states);
        compute_next_states(current_frame, new_bad_states, state_set);


        // If state is not relative inductive then do a recursive step
        if (!vset_is_empty(new_bad_states)) {
            recursive_remove_states(counter_example, new_bad_states, current_frame->prev);

            // Check if the recursive step returns a counter example
            // if this is the case then directly return it
            if (!vset_is_empty(counter_example)) {
                print_state_f(state);
                Printf(info, "\n");
                //Warning(info, "[recursive_remove_states] Intersection with initial states");
                return;
            }

            // Add all forward propagated states that are still relative inductive
            // to the next forward propagation set and remove them from this frame.
            //
            // compute pre-image of the next frame that intersects with the relative inductive
            // states of the previous frame to find the non-relative inductive states in this frame.
            // and remove these from the previous relative inductive states to find the states
            // that are still relative inductive and add them for forward propagation.
            assert(current_frame != NULL);
            assert(current_frame->next != NULL);

            if (refine_strategy == REV_PDR || refine_strategy == REV_PDR_INTERLEAVED) {
                post(propagated_states, current_frame->next->states, new_bad_states);
            } else {
                pre(propagated_states, current_frame->next->states, new_bad_states);
            }


            vset_minus(new_bad_states, propagated_states);

            vset_minus(current_frame->states, new_bad_states);
            vset_union(bad_states, new_bad_states);
        }
        // the state is relative inductive to the previous frame, either since
        // it is already relative inductive at the start OR it is now relative inductive
        // after the recursive step removed all states from the pre-image from the previous frame
        // (otherwise a counterexample would have been found)

        // it is now necessary to generalize the state as far as possible.
        generalize(state_set, state, current_frame);

        // remove states not reachable from previous frame from current frame
        vset_minus(current_frame->states, state_set);
        // add the generalized state to the set for forward propagation
        vset_union(bad_states, state_set);

        // remove all states in the generalized state set from the unvisited states
        // since we know they are relative inductive.
        vset_minus(unvisited_states, state_set);

        // clear state set so we can add a new state in the next iteration
        vset_clear(state_set);
    }

    assert(!vset_is_empty(bad_states));

    vset_destroy(propagated_states);
    vset_destroy(new_bad_states);
    vset_destroy(state_set);
    vset_destroy(unvisited_states);

    free(state);
}


void init_source_and_goal_states(vset_t I, vset_t P, vset_t U) {
    vset_t notP = empty();
    vset_copy(notP, U);
    vset_minus(notP, P);

    source_states = empty();
    goal_states = empty();

    if (using_reverse_pdr) {
        vset_copy(source_states, I);
        vset_copy(goal_states, notP);
    } else {
        vset_copy(source_states, notP);
        vset_copy(goal_states, I);
    }
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
property_directed_reachability(vset_t I, vset_t P, vset_t U)
{
    Warning(info, "Initialize PDR");

    using_reverse_pdr = (refine_strategy == REV_PDR || refine_strategy == REV_PDR_INTERLEAVED);

    g_universe = U;

    vset_t bad_state_set = empty();
    vset_t seen_states = empty();
    vset_t counter_example = empty();

    init_source_and_goal_states(I, P, U);

    frame *frame_initial = frame_create(goal_states);
    frame *total = frame_create(U);

    insert_after(frame_initial, total);

    frame *current_frame = total;

    int *bad_state = malloc(sizeof(int) * N);

    vset_count_info(I);
    vset_count_info(P);

    bool has_bad_state;
    int depth = 0;
    Warning(info, "[pdr] Checking depth %d", depth);
    while(true) {
        has_bad_state = get_bad_state(bad_state, source_states, seen_states);

        if (!has_bad_state) {
            // Create new frame
            frame* new_frame = frame_create(U);
            insert_after(total, new_frame);

            vset_clear(seen_states);

            current_frame = total;
            total = new_frame;

            depth++;

            compute_frame_sizes(total);

            Warning(info, "[pdr] Checking depth %d", depth);
            continue;
        }

        vset_add(bad_state_set, bad_state);
        assert(!contains_goal(bad_state_set));

        if (!vset_is_empty(bad_state_set)) {
            recursive_remove_states(counter_example, bad_state_set, current_frame);

            if (!vset_is_empty(counter_example)) {
                return false;
            }
            vset_union(seen_states, bad_state_set);
        }

        vset_clear(bad_state_set);

        // Propagate removed states backwards
        if (propagate_removed_states(total->prev)) {
            if (using_reverse_pdr) {
                vset_copy(bad_state_set, U);
                vset_minus(bad_state_set, invariant_states);
                vset_copy(invariant_states, bad_state_set);
            }
            return verify_invariant(invariant_states, P, U);
        }
    }
}


#else

#endif

