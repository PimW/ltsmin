#include <aux/options.h>
#include "pdr-util.h"
#include <pins2lts-sym/alg/aux.h>

void
vset_count_info(vset_t set)
{
    long count;
    long double el;
    vset_count_fn(set, &count, &el);
    Warning (info, "nodes: %ld\t\t states: %.0Lf", count, el);
}

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

void
print_state_f (int *state)
{
    for (int l = 0; l < N; l++) {
        Printf (info, "%2d,", state[l]);
    }
}

static void
print_state_cb (void *ctx, int *state)
{
    for (int l = 0; l < N; l++) {
        Printf (info, "%2d,", state[l]);
    }
    Printf(info, "\n");
}

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

//void
//print_state_cb (void *context, int *src)
//{
//    int group = *(int *)context;
//    Statef (info, src, inv_proj[group]);
//    Warning (info, " (%d)\n", group);
//}