#include <aux/options.h>
#include "reverse-reach.h"
#include "pdr-util.h"

vset_t bad_states;

/**
 * Takes all states in U that do not satisfy P
 * @return a set of bad states
 */
void
get_bad_states(vset_t bad_states, vset_t U, vset_t P)
{
    vset_copy(bad_states, U);
    vset_minus(bad_states, P);
}


bool
reverse_reach(vset_t I, vset_t P, vset_t U)
{
    long node_count = 0;

    if (bad_states == NULL) {
        bad_states = empty();
    }

    vset_t V_old = empty();
    vset_t V = empty();

    get_bad_states(V, U, P);
    vset_union(V, bad_states);

    int level = 0;
    while (!vset_equal(V_old, V)) {
        if (log_active(info)) {
            vset_node_count(&node_count, V);
            if (node_count > max_node_count) {
                max_node_count = node_count;
            }
        }
        vset_copy(V_old, V);
        pre(V, V, U);
        level++;
    }

    vset_minus(V_old, I);
    if (!vset_equal(V_old, V)) {
        return false;
    }

    vset_minus(U, V);
    if (log_active(info)) {
        vset_node_count(&node_count, U);
        if (node_count > max_node_count) {
            max_node_count = node_count;
        }
    }
    vset_copy(bad_states, V);

    vset_destroy(V_old);
    vset_destroy(V);

    Warning(info, "[reverse_reach] Found Invariant");

    return true;
}