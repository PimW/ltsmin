#ifndef PINS2LTS_SYM_PDR_UTIL_H
#define PINS2LTS_SYM_PDR_UTIL_H

extern void vset_count_info(vset_t set);
extern void vset_node_count(long *node_count, vset_t set);
extern inline vset_t empty();
extern void post(vset_t dst, vset_t source, vset_t universe);
extern void pre(vset_t dst, vset_t source, vset_t universe);
extern void print_state_f(int *state);
extern void print_state_cb (void *ctx, int *state);
extern bool verify_invariant(vset_t invariant_states, vset_t P, vset_t universe);

#endif //PINS2LTS_SYM_PDR_UTIL_H
