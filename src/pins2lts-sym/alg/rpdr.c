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

rt_timer_t pdr_timer;
rt_timer_t generalize_timer;
rt_timer_t image_timer;

/*
 * Frame linked list structure and operations
 */
typedef struct frame
{
    vset_t states;
    struct frame* next;
    struct frame* prev;
} frame;

static void
print_state (int *state)
{
    for (int l = 0; l < N; l++) {
        Printf (info, "%2d,", state[l]);
    }
}

static void
print_state_cb (void *ctx, int *state)
{
    //Printf(info, ">");
    for (int l = 0; l < N; l++) {
        Printf (info, "%2d,", state[l]);
    }
    Printf(info, "\n");
}

static inline vset_t
empty ()
{
    return vset_create (domain, -1, NULL);
}


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

    if (new->prev != NULL) {
        new->prev->next = new;
    }
    new->next->prev = new;
}

void
insert_after(frame *list, frame *new)
{
    new->next = list->next;
    new->prev = list;

    new->prev->next = new;
    if (new->next != NULL) {
        new->next->prev = new;
    }
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

bool
get_bad_state(int *state, vset_t universe, vset_t P, vset_t seen)
{
    vset_t unseen_states = empty();

    vset_copy(unseen_states, universe);
    vset_minus(unseen_states, P);
    vset_minus(unseen_states, seen);

    if (!vset_is_empty(unseen_states)) {
        //vset_random(unseen_states, state);
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
contains_initial(vset_t states)
{
    vset_t tmp = empty();

    vset_copy(tmp, states);
    vset_intersect(tmp, g_initial);

    bool result = (bool)vset_is_empty(tmp);

    vset_destroy(tmp);

    return !result;
}

/**
 * Checks relative-inductiveness of states to frame f.
 * This means that Post(states) /\ f->states = 0
 */
bool
is_relative_inductive(vset_t states, frame *f)
{
    vset_t tmp = empty();

    post(tmp, f->prev->states, states); // Post(prev(current_frame).states) /\ states // TODO: check if prev is faster
    //pre(tmp, states, f->prev->states);

    bool val =  (bool) vset_is_empty(tmp); // == 0
    vset_destroy(tmp);
    return val;
}


//bool
//is_relative_inductive_for_var(vset_t states, frame *f, int var)
//{
//    vset_t          temp = empty ();
//
//    for (int i = 0; i < nGrps; i++) {
//        if (ci_binary_search(w_projs[i], var) != -1) {
//            vset_next (temp, f->prev->states, group_next[i]);
//            vset_intersect(temp, states);
//            if (!vset_is_empty(temp)) {
//                vset_destroy (temp);
//                return false;
//            }
//        }
//    }
//    vset_destroy (temp);
//    return true;
//}


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
generalize(vset_t result_states, int* state, frame *current_frame)
{
    ci_list *projection = ci_create((size_t)total_proj->count); // TODO: add size of base/full projection
    ci_list *tmp_projection = ci_create((size_t)total_proj->count);

    vset_clear(result_states);
    vset_add(result_states, state);

    ci_copy(projection, total_proj);

    vset_t generalized_states = empty();

    assert(!contains_initial(result_states));
    assert(is_relative_inductive(result_states, current_frame));

    //for (int i = 0; i < nGrps; i++) {
    for (int i = 0; i < N; i++) {
        ci_copy(tmp_projection, projection);
        ci_remove(tmp_projection, ci_binary_search(tmp_projection, i));
        //ci_minus(tmp_projection, r_projs[i]);


        // Project the bad state to a state defined only on the vars in the projection
        int *projected_state = malloc(sizeof(int) * tmp_projection->count);
        ci_project(projected_state, state, tmp_projection);

        assert(!vset_is_empty(result_states));

        vset_copy_match(generalized_states, g_universe, tmp_projection->count, tmp_projection->data, projected_state);
        assert(!vset_is_empty(generalized_states));

        if (!contains_initial(generalized_states)
            // && is_relative_inductive_for_var(generalized_states, current_frame, i)) {
            && is_relative_inductive(generalized_states, current_frame)) {
            ci_copy(projection, tmp_projection);
            vset_copy(result_states, generalized_states);
        }
    }
//    Warning(info, "[generalize] generalized states count: ");
//    vset_count_info(result_states);

    vset_destroy(generalized_states);

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

    int i = 0;
    while (f->prev != NULL) {
        //Warning(info, "[propagate_remove_states] frame %d size:", i);
        //vset_count_info(f->states);

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
print_frame_sizes(frame *frame)
{
    struct frame *f = frame;

    int i = 0;
    // TODO: output frame sizes
    while (f->prev != NULL) {
        Warning(info, "[print_frame_sizes] frame %d size:", i);
        vset_count_info(f->states);
        f = f->prev;
        i++;
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
    //Warning(info, "[recursive_remove_states] Initial unvisited state count: ");
    //vset_count_info(unvisited_states);

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
        //vset_random(unvisited_states, state);
        vset_add(state_set, state);

        // Compute pre-image for the bad state and intersect it with the previous frame
        vset_clear(new_bad_states);
        pre(new_bad_states, state_set, current_frame->prev->states);

        // If state is not relative inductive then do a recursive step
        if (!vset_is_empty(new_bad_states)) {
            recursive_remove_states(counter_example, new_bad_states, current_frame->prev);

            // Check if the recursive step returns a counter example
            // if this is the case then directly return it
            if (!vset_is_empty(counter_example)) {
                print_state(state);
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

            RTstartTimer(image_timer);

            pre(propagated_states, current_frame->next->states, new_bad_states);
            RTstopTimer(image_timer);

            vset_minus(new_bad_states, propagated_states);

            vset_minus(current_frame->states, new_bad_states);
            vset_union(bad_states, new_bad_states);
        }
        // the state is relative inductive to the previous frame, either since
        // it is already relative inductive at the start OR it is now relative inductive
        // after the recursive step removed all states from the pre-image from the previous frame
        // (otherwise a counterexample would have been found)


        RTstartTimer(generalize_timer);
        // it is now necessary to generalize the state as far as possible.
        generalize(state_set, state, current_frame);
        RTstopTimer(generalize_timer);

        // remove states not reachable from previous frame from current frame
        vset_minus(current_frame->states, state_set);
        // add the generalized state to the set for forward propagation
        vset_union(bad_states, state_set);

        // remove all states in the generalized state set from the unvisited states
        // since we know they are relative inductive.
        vset_minus(unvisited_states, state_set);

//        Warning(info, "[recursive_remove_states] Unvisited states count: ");
//        vset_count_info(unvisited_states);

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
property_directed_reachability(vset_t I, vset_t P, vset_t universe)
{
    Warning(info, "Initialize PDR");

    pdr_timer = RTcreateTimer();
    generalize_timer = RTcreateTimer();
    image_timer = RTcreateTimer();

    g_universe = universe;
    g_initial = I;

    frame *frame_initial = RTmallocZero (sizeof(frame));
    frame_initial->states = empty();
    vset_copy(frame_initial->states, I);

    frame *total = RTmallocZero (sizeof(frame));

    vset_t total_states = empty();
    vset_copy(total_states, universe);
    total->states = total_states;

    frame_initial->next = total;
    total->prev = frame_initial;

    frame *current_frame = total;

    vset_t bad_state_set = empty();
    vset_t seen_states = empty();
    vset_t counter_example = empty();

    int *bad_state = malloc(sizeof(int) * N);

    vset_count_info(I);
    vset_count_info(P);
    vset_count_info(universe);
    vset_count_info(total->states);

    bool has_bad_state;
    int depth = 0;
    Warning(info, "[pdr] Checking depth %d", depth);
    while(true) {
        RTstartTimer(pdr_timer);
//        Warning(info, "pdr: Checking depth %d", depth);
//        Warning(info, "pdr: States seen until now: ");
//        vset_count_info(seen_states);
        has_bad_state = get_bad_state(bad_state, universe, P, seen_states);
//        Warning(info, "pdr: Random bad state: ");
//        print_state(bad_state);
//        Printf(info, "\n");

        if (!has_bad_state) {
            RTstopTimer(pdr_timer);

            RTprintTimer(info, pdr_timer, "pdr time: ");
            RTprintTimer(info, generalize_timer, "generalize time: ");
            RTprintTimer(info, image_timer, "pre-image time: ");

            RTresetTimer(pdr_timer);
            RTresetTimer(image_timer);
            RTresetTimer(generalize_timer);

            print_frame_sizes(total);
            Warning(info, "[pdr] Creating new frame");
            // Create new frame
            frame* new_frame = RTmallocZero (sizeof(frame));
            new_frame->states = empty();
            vset_copy(new_frame->states, universe);

            insert_after(total, new_frame);
            vset_clear(seen_states);

            current_frame = total;
            total = new_frame;

            depth++;
            Warning(info, "[pdr] Checking depth %d", depth);
            continue;
        }

        vset_add(bad_state_set, bad_state);
        assert(!contains_initial(bad_state_set));

        if (!vset_is_empty(bad_state_set)) {
            recursive_remove_states(counter_example, bad_state_set, current_frame);

            if (!vset_is_empty(counter_example)) {
                return false;
            }
            vset_union(seen_states, bad_state_set);
        }

        vset_clear(bad_state_set);

        // Warning(info, "[pdr] Propagate removed states..");
        // Propagate removed states backwards
        if (propagate_removed_states(total->prev)) {
            // All code beyond this is just verifying the invariant
            Warning(info, "pdr: Verifying invariant: ");

            assert(!vset_is_empty(invariant_states));

            vset_t inv = empty();
            Warning(info, "pdr: Checking inductiveness...");
            post(inv, invariant_states, universe);
            vset_minus(inv, invariant_states);

            Warning(info, "pdr: Checking soundness...");
            vset_t tmp_invariant_states = empty();
            vset_copy(tmp_invariant_states, invariant_states);
            vset_minus(tmp_invariant_states, P);

            if (vset_is_empty(inv) && vset_is_empty(tmp_invariant_states)) {
                Warning(info, "pdr: invariant found");
                vset_count_info(invariant_states);
                vset_copy(universe, invariant_states);
                return true;
            } else {
                Warning(info, "pdr: error");
                exit(0);
            }
        }
    }
}


vset_t bad_states;

bool
reverse_reach(vset_t I, vset_t P, vset_t U)
{
    if (bad_states == NULL) {
        bad_states = empty();
    }

    vset_t V_old = vset_create(domain, -1, NULL);
    vset_t V = vset_create(domain, -1, NULL);

    get_bad_states(V, U, P);
    vset_union(V, bad_states);

    int level = 0;
    while (!vset_equal(V_old, V)) {
        vset_copy(V_old, V);
        pre(V, V, U);
        level++;
    }

    vset_minus(V_old, I);
    if (!vset_equal(V_old, V)) {
        return false;
    }

    vset_copy(U, V);
    vset_copy(bad_states, V);

    return true;
}


#else

bool reach_reverse_pdr(vset_t I)
{
    Warning(info, "Couldn't find sylvan");
    return false;
}

#endif
