#include <aux/options.h>
#include "pdr-util.h"
#include <pins2lts-sym/alg/aux.h>

/**
 * Compute and output the amount of nodes and states in a set.
 *
 * @param set
 */
void
vset_count_info(vset_t set)
{
    long count;
    long double el;
    vset_count_fn(set, &count, &el);
    Warning (info, "nodes: %ld\t\t states: %.0Lf", count, el);
}

/**
 * Computes and returns the amount of nodes in a set.
 *
 * @param node_count
 * @param set
 * @return node_count
 */
void
vset_node_count(long *node_count, vset_t set)
{
    long double el;
    vset_count_fn(set, node_count, &el);
}

/**
 * Create an empty vset with the default domain.
 *
 * @return Empty allocated vset
 */
inline vset_t
empty ()
{
    return vset_create (domain, -1, NULL);
}

/**
 * Calculates the image of a set
 *
 * @param dst
 * @param source
 * @param universe
 */
void
post(vset_t dst, vset_t source, vset_t universe)
{
    add_step(false, dst, source, universe);
}

/**
 * Compute pre-image of a set
 *
 * @param dst
 * @param source
 * @param universe
 */
void
pre(vset_t dst, vset_t source, vset_t universe)
{
    add_step(true, dst, source, universe);
}

/**
 * Print a state from an array of integers
 *
 * @param state
 */
void
print_state_f (int *state)
{
    for (int l = 0; l < N; l++) {
        Printf (info, "%2d,", state[l]);
    }
}

/**
 * Print state callback method, wrapper around print_state_f
 * to use with the vset_enum method.
 *
 * @param ctx argument required by vset_enum (unused)
 * @param state argument passed by vset_enum
 */
void
print_state_cb (void *ctx, int *state)
{
    print_state_f(state);
    Printf(info, "\n");
}

/**
 * Verify an invariant, this checks:
 *  1) invariant <= P (invariant contains only safe states)
 *  2) post(invariant) <= invariant (invariant has not transitions to non-invariant states)
 *  3) count(invariant) != 0 (invariant should not be empty)
 *
 * @param invariant_states
 * @param P
 * @param universe
 * @return bool true if invariant is valid.
 */
bool
verify_invariant(vset_t invariant_states, vset_t P, vset_t universe) {
    Warning(info, "[pdr] Verifying invariant: ");

    assert(!vset_is_empty(invariant_states));

    vset_t inv = empty();
    vset_t tmp_invariant_states = empty();

    Warning(info, "[pdr] Checking inductiveness...");
    post(inv, invariant_states, universe);
    vset_minus(inv, invariant_states);
    assert(vset_is_empty(inv));

    Warning(info, "[pdr] Checking soundness...");
    vset_copy(tmp_invariant_states, invariant_states);
    vset_minus(tmp_invariant_states, P);

    if (vset_is_empty(inv) && vset_is_empty(tmp_invariant_states)) {
        Warning(info, "[pdr] invariant found");
        vset_count_info(invariant_states);
        vset_copy(universe, invariant_states);
    } else {
        Warning(info, "[pdr] error");
        exit(0);
    }

    vset_destroy(inv);
    vset_destroy(tmp_invariant_states);

    return true;
}