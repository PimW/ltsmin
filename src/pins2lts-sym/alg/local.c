#include <hre/config.h>

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
#include <pins2lts-sym/alg/local.h>
#include <pins2lts-sym/aux/options.h>
#include <pins2lts-sym/aux/output.h>
#include <ltsmin-lib/ltsmin-standard.h>
#include <ltsmin-lib/ltsmin-syntax.h>
#include <ltsmin-lib/ltsmin-tl.h>
#include <mc-lib/atomics.h>
#include <mc-lib/bitvector-ll.h>
#include <util-lib/bitset.h>
#include <util-lib/dfs-stack.h>
#include <util-lib/util.h>
#include <aux/prop.h>

#include <alg/rpdr.h>
#include <sylvan.h>


#include <signal.h>


#include <time.h>






/**
 * TODO:
 * [ ] Learn only new transitions (rest transition relation)
 *    [ ] Project to the union of read and write projections
 *    [ ] Improve next-state function to allow different projections
 * [ ] Restrict queue sets to the right program counter
 * [ ] Try grouping by process
 * [ ] Try group merging
 * [ ] Chaining
 * [ ] Saturation
 * [ ] Full visited sets vs. New level
 */






/**
 * List of "writer groups"
 * Each element in turn is a list of "reader groups", reading from the
 * respective writer group. The slots intersection of the read and write
 * support of the respective groups are also recorded.
 */
typedef struct write_group_s {
    int index;
    int num_readers;
    struct reader_group_s {
        int         index; // reader
        ci_list    *slots;
        ci_list    *compl;
        vset_t      tmp;
        vset_t      complement;
    } *readers;
    vset_t      complement;     // to create visited set
} write_group_t;

static write_group_t *writers;

typedef struct reader_group_s reader_t;

static inline write_group_t *
w_bgn()
{
    return &writers[0];
}

static inline write_group_t *
w_end()
{
    return &writers[nGrps];
}

static inline reader_t *
r_bgn(write_group_t *wg)
{
    return &wg->readers[0];
}

static inline reader_t *
r_end(write_group_t *wg)
{
    return &wg->readers[wg->num_readers];
}

static vset_t *exact_explored;     // visited write

static vset_t *V_w;     // visited write
static vset_t *Q_w;     // queue   write
static vset_t *C_w;     // complement write

static vset_t *V_r;     // visited read
static vset_t *Q_r;     // queue   read
static vset_t *X_r;     // temp    read
static vset_t *Y_r;     // temp 2  read

static vset_t *N_r;     // new transitions
static vset_t *C_r;     // complement write set

static vset_t *V_old_r;     // visited old
static vset_t  X;

// Sets for vset_next
static vset_t source_set;
static vset_t image_set;
static vset_t initial_set;

// Complement projections
ci_list **r_compl_projs;
ci_list **w_compl_projs;


static ci_list **rrows;
static ci_list **wrows;

static int explored = 0;

typedef struct group_add_s {
    int    group;
    int   *src;
} group_add_t;

ci_list *p_all;

static void
Statef (log_t log, int *state, ci_list *proj)
{
    if (!log_active(log)) return;
    int p = 0;
    for (int l = 0; l < N; l++) {
        if (p < proj->count && proj->data[p] == l) {
            Printf (log, "%2d,", state[p]);
            p++;
        } else {
            Printf (log, " *,");
        }
    }
}


void
print_state_r (void *context, int *src)
{
    int group = *(int *)context;
    Statef (info, src, r_projs[group]);
    Warning (info, " (%d)\n", group);
}

void
print_state_w (void *context, int *src)
{
    int group = *(int *)context;
    Statef (info, src, w_projs[group]);
    Printf (info, " (%d)\n", group);
}


static void
group_add_old (void *context, transition_info_t *ti, int *dst, int *cpy)
{
    group_add_t        *ctx = (group_add_t *) context;

    vrel_add_cpy (group_next[ctx->group], ctx->src, dst, cpy);
    vset_add (Q_w[ctx->group], dst);
    Statef (debug, ctx->src, r_projs[ctx->group]);
    Printf (debug, " -(%2d)-> ", ctx->group);
    Statef (debug, dst, w_projs[ctx->group]);
    Printf (debug, "\n");
    (void) ti;
}


static void
group_add (void *context, transition_info_t *ti, int *dst, int *cpy)
{
    group_add_t        *ctx = (group_add_t *) context;

    ci_list *row = wrows[ctx->group];
    vset_add (Q_w[ctx->group], dst);
    int dst_short[row->count];
    int cpy_short[row->count];
    for (int i = 0; i < row->count; i++) {
        int j = ci_get(row,i);
        dst_short[i] = dst[j];
        cpy_short[i] = cpy[j];
    }
    vrel_add_cpy (group_next[ctx->group], ctx->src, dst_short, cpy_short);
    vset_add (Q_w[ctx->group], dst_short);

    Statef (debug, ctx->src, r_projs[ctx->group]);
    Printf (debug, " -(%2d)-> ", ctx->group);
    Statef (debug, dst_short, w_projs[ctx->group]);
    Printf (debug, "\n");
    (void) ti;
}

void
group_add3 (void *context, transition_info_t *ti, int *dst, int *cpy)
{
    group_add_t        *ctx = (group_add_t *) context;

    Statef (debug, ctx->src, p_all);
    Printf (debug, " -(%2d)-> ", ctx->group);
    Statef (debug, dst, p_all);
    Printf (debug, "\n");
    (void) ti; (void) cpy;
}



void
print_next_state (void *context, int *src)
{
    group_add_t         ctx;
    ctx.group = *(int *)context;
    ctx.src = src;
    GBgetTransitionsLong (model, ctx.group, src, group_add3, &ctx);
}

static void
explore_cb (void *context, int *src)
{
    clock_t t1, t2;
    t1 = clock();
    long elapsed;

    explored++;
    group_add_t         ctx;
    ctx.group = *(int *)context;
    int src_long[N];
    ctx.src = src;
    //print_state_r(&ctx.group, src);

    GBgetTransitionsShortR2W (model, ctx.group, src, group_add_old, &ctx);
    //explored++;


//    ci_list *row = rrows[ctx.group];
//    for (int i = 0; i < row->count; i++) {
//        src_long[ci_get(row,i)] = src[i];
//    }
//    guard_t *gs = GBgetGuard(model, ctx.group);
//    for (int i = 0; i < gs->count; i++) {
//        int g = gs->guard[i];
//        int v = GBgetStateLabelLong(model, g, src_long);
//        if (v == 0 || v == 2) return; // group disabled or won't evaluate
//        // (the state is unreachable assuming absence of modeling errors.)
//        if (v == 2) HREassert(false);
//    }
//    GBgetActionsLong(model, ctx.group, src_long, group_add, &ctx);

    t2 = clock();
    elapsed = t2 - t1;
    //Warning(info, "elapsed: %ld ms\n", elapsed);
}

static void vset_count_info(vset_t set, int group,  int level)
{
    long count;
    long double el;
    vset_count_fn(set, &count, &el);
    Warning (info, "level: %ld\t\t group: %ld\t\t nodes: %ld\t\t states: %.0Lf", level, group, count, el);
}

/**
 * Assumes
 */
static void learn_new_transitions_for_group (int i)
{
    vset_enum    (N_r[i], explore_cb, &i);
}

static void apply_transition_relation_to_group (int i)
{
    vset_join    (source_set, Q_r[i], C_r[i]);
    vset_next    (image_set, source_set, group_next[i]);
    vset_project (Q_w[i], image_set);
}

static bool recombine_new_states_for_group (int i)
{
    bool fanout = false;
    write_group_t *wg = &writers[i];
    for (reader_t *r = r_bgn(wg); r <  r_end(wg); r++) {
        int j = r->index;
        if (r->tmp == NULL) { // writer's domain overlaps reader
            vset_project (X_r[j], Q_w[i]);
            //vset_minus   (X_r[j], V_r[j]);
            long n1;
            long double e1;
            vset_count_fn (X_r[j], &n1, &e1);
            if (e1 > 0)
            Warning (infoLong, "_ X _ === _ --> %.0Lf\t\t%d>%d", e1, i, j);
            fanout |= !vset_is_empty(X_r[j]);
            vset_union   (Y_r[j], X_r[j]);
            vset_clear   (X_r[j]);
        } else {
            long n1, n2, n3, n4;
            long double e1, e2, e3, e4;

            vset_project(r->tmp, Q_w[i]); // r_j w_i (Post(Q_r[i]))
            vset_count_fn (r->tmp, &n1, &e1);
            if (e1 != 0) {
                vset_project        (r->complement, V_r[j]);    // r_j -w_i (V_r[i])

                vset_join (X_r[j], r->complement, r->tmp);

                fanout |= !vset_is_empty(X_r[j]);
                vset_union          (Y_r[j],        X_r[j]);

                vset_clear (X_r[j]);
                vset_clear (r->complement);
            }
            vset_clear (r->tmp);
        }
    }
    return fanout;
}

void add_states_from_group_to_group(int i, int dest)
{

    write_group_t *wg = &writers[i];
    for (reader_t *r = r_bgn(wg); r <  r_end(wg); r++) {
        int j = r->index;
        if (j == dest) {
            if (r->tmp == NULL) { // writer's domain overlaps reader
                vset_project (X_r[j], Q_w[i]);
                //vset_minus   (X_r[j], V_r[j]);
                long n1;
                long double e1;
                vset_count_fn (X_r[j], &n1, &e1);
                if (e1 > 0)
                Warning (infoLong, "_ X _ === _ --> %.0Lf\t\t%d>%d", e1, i, j);

                vset_union   (Y_r[j], X_r[j]);
                vset_clear   (X_r[j]);
            } else {
                long n1, n2, n3, n4;
                long double e1, e2, e3, e4;

                vset_project(r->tmp, Q_w[i]); // r_j w_i (Post(Q_r[i]))
                vset_count_fn (r->tmp, &n1, &e1);
                if (e1 != 0) {
                    vset_project        (r->complement, V_r[j]);    // r_j -w_i (V_r[i])

                    vset_join (X_r[j], r->complement, r->tmp);

                    vset_union          (Y_r[j],        X_r[j]);

                    vset_clear (X_r[j]);
                    vset_clear (r->complement);
                }
                vset_clear (r->tmp);
            }
        }
    }
}

int reach_local_sat(vset_t I, vset_t V)
{
    Warning(info, "Using saturation");
    int                 level = 0;
    bool                all_done;

    do { // while \exists_i \in [1..K] : Q^r_i != 0 do
        level++;
        all_done = true;

        Warning(info, "Approx Reach level: %d", level);
        for (int i = 0; i < nGrps; i++) {
            //write_group_t      *wg = &writers[i];
            vset_clear   (Q_w[i]);
            vset_clear   (V_w[i]);


            while (true) {
                //all_done &= vset_is_empty(N_r[i]);

                learn_new_transitions_for_group(i);
                vset_union(V_w[i], Q_w[i]);

                apply_transition_relation_to_group(i);

                //recombine_new_states_for_group(i);


                // Add new states only for group i
                add_states_from_group_to_group(i, i);
                /*
//                write_group_t *wg = &writers[i];
//                for (reader_t *r = r_bgn(wg); r <  r_end(wg); r++) {
//                    int j = r->index;
//                    if (j == i) {
//                        if (r->tmp == NULL) { // writer's domain overlaps reader
//                            vset_project (X_r[j], Q_w[i]);
//                            //vset_minus   (X_r[j], V_r[j]);
//                            long n1;
//                            long double e1;
//                            vset_count_fn (X_r[j], &n1, &e1);
//                            if (e1 > 0)
//                            Warning (infoLong, "_ X _ === _ --> %.0Lf\t\t%d>%d", e1, i, j);
//                            vset_union   (Y_r[j], X_r[j]);
//                            vset_clear   (X_r[j]);
//                        } else {
//                            long n1, n2, n3, n4;
//                            long double e1, e2, e3, e4;
//
//                            vset_project(r->tmp, Q_w[i]); // r_j w_i (Post(Q_r[i]))
//                            vset_count_fn (r->tmp, &n1, &e1);
//                            if (e1 != 0) {
//                                vset_project        (r->complement, V_r[j]);    // r_j -w_i (V_r[i])
//
//                                vset_join (X_r[j], r->complement, r->tmp);
//
//                                vset_union          (Y_r[j],        X_r[j]);
//
//                                vset_clear (X_r[j]);
//                                vset_clear (r->complement);
//                            }
//                            vset_clear (r->tmp);
//                        }
//                    }
//
//
//                }
                 */

                if (vset_is_empty(Y_r[i])) {
                    break;
                }

                vset_clear(Q_r[i]);
                vset_clear(N_r[i]);
                vset_copy(Q_r[i], Y_r[i]);
                vset_copy(N_r[i], Y_r[i]);

                vset_clear(Y_r[i]);

                vset_minus(N_r[i], V_r[i]);
                vset_union(V_r[i], Q_r[i]);

                //all_done &= vset_equal (V_old_r[i], V_r[i]);
                //all_done &= vset_is_empty(Q_w[i]);

            }

            vset_copy(V_old_r[i], V_r[i]);

            vset_copy(Q_w[i], V_w[i]);

            // Add new states for all groups at the end to make sure we only have to recombine once.
            recombine_new_states_for_group(i);

            for (int j = 0; j < nGrps; j++) {
                vset_union(Q_r[j], Y_r[j]);// N_r[j] is always a subset of Q_r[j]

                //all_done &= vset_is_empty(Y_r[j]);

                vset_minus(Y_r[j], V_r[j]);
                vset_union(N_r[j], Y_r[j]);
                //all_done &= vset_is_empty(N_r[j]);
            }
            for (int j = 0; j < nGrps; j++) {
                all_done &= vset_is_empty (N_r[j]);
            }

        }

        //vset_reorder (domain);

    } while (!all_done);


    Warning(info, "Final states: ");
    for (int i = 0; i < nGrps; i++) {
        vset_count_info(V_r[i], i, level);;
    }

    Warning(info, "Next state called %d times!", explored)
    
    return level;
    (void) V;
}


int
reach_local (vset_t I, vset_t V)
{
    int                 level = 0;
    bool                all_done;

    do { // while \exists_i \in [1..K] : Q^r_i != 0 do
        level++;
        all_done = true;

        Warning(info, "Approx Reach level: %d", level);
        for (int i = 0; i < nGrps; i++) {
            //write_group_t      *wg = &writers[i];
            vset_clear   (Q_w[i]);

            learn_new_transitions_for_group(i);

            apply_transition_relation_to_group(i);

            recombine_new_states_for_group(i);

            if (strategy == CHAIN || strategy == CHAIN_P) {
                for (int j = i + 1; j < nGrps; j++) {       // don't add states for already used groups
                    vset_union(Q_r[j], Y_r[j]);             // N_r[j] is always a subset of Q_r[j]

                    vset_minus(Y_r[j], V_r[j]);
                    vset_union(N_r[j], Y_r[j]);

                    vset_union(V_r[j], Q_r[j]);  // Q_r[j] hasn't changed
                }
            }
/*
//            vset_enum    (N_r[i], explore_cb, &i);
//
//            vset_join(source_set, Q_r[i], C_r[i]);
//
//            vset_next(image_set, source_set, group_next[i]);
//            vset_project(Q_w[i], image_set);

            //vset_union   (V_w[i], Q_w[i]);

//            write_group_t *wg = &writers[i];
//            for (reader_t *r = r_bgn(wg); r <  r_end(wg); r++) {
//                int j = r->index;
//                if (r->tmp == NULL) { // writer's domain overlaps reader
//                    vset_project (X_r[j], Q_w[i]);
//                    //vset_minus   (X_r[j], V_r[j]);
//                    long n1;
//                    long double e1;
//                    vset_count_fn (X_r[j], &n1, &e1);
//                    if (e1 > 0)
//                    Warning (infoLong, "_ X _ === _ --> %.0Lf\t\t%d>%d", e1, i, j);
//                    vset_union   (Y_r[j], X_r[j]);
//                    vset_clear   (X_r[j]);
//                } else {
//                    long n1, n2, n3, n4;
//                    long double e1, e2, e3, e4;
//
//                    vset_project(r->tmp, Q_w[i]); // r_j w_i (Post(Q_r[i]))
//                    vset_count_fn (r->tmp, &n1, &e1);
//                    if (e1 != 0) {
//                        vset_project        (r->complement, V_r[j]);    // r_j -w_i (V_r[i])
//
//                        vset_join (X_r[j], r->complement, r->tmp);
//
//                        vset_union          (Y_r[j],        X_r[j]);
//
//                        vset_clear (X_r[j]);
//                        vset_clear (r->complement);
//                    }
//                    vset_clear (r->tmp);
//                }
//            } */
        }

        //vset_reorder (domain);

        for (int i = 0; i < nGrps; i++) {
            vset_clear(Q_r[i]);
            vset_copy(Q_r[i], Y_r[i]);
            vset_copy(N_r[i], Y_r[i]);

            vset_clear(Y_r[i]);

            vset_minus(N_r[i], V_r[i]);
            vset_union(V_r[i], Q_r[i]);

            if (strategy != BFS_P && strategy != CHAIN_P) {
                //Warning(info, "Using full visited state set");
                vset_copy(Q_r[i], V_r[i]);
            }

            all_done &= vset_equal (V_old_r[i], V_r[i]);
            vset_copy(V_old_r[i], V_r[i]);
        }

    } while (!all_done);


    Warning(info, "Final states: ");
    for (int i = 0; i < nGrps; i++) {
        vset_count_info(V_r[i], i, level);;
    }

    Warning(info, "Next state called %d times!", explored)

//    vset_clear(states);
//    for (int i = 0; i < nGrps; i++) {
//        vset_union(states, V_r[i]);
//    }
//
//    for (int i = 0; i < nGrps; i++) {
//        vset_count_info(V_r[i], i, level);
//        vset_intersect(states, V_r[i]);
//    }
//    Warning(info, "Total full states: ");
//    vset_count_info(states, -1, level);


//    Warning(info, "Checking invariants");
//    vset_t unsafe = vset_create (domain, inv_proj[0]->count, inv_proj[0]->data);
//
//    Warning(info, "Finding counter-examples");
//    find_counter_examples(states, unsafe);
//
//    vset_t U = vset_create(domain, -1, NULL);
//
//    vset_union(U, unsafe);
//
//    vset_destroy(unsafe);

    //Warning(info, "Running PDR");
    //reach_pdr(I, U, states, level);

//    Warning(info, "Traditional invariant check");
//    check_invariants(states, level);

    return level;
    (void) V;
}

/**
 * For each group i, this function finds all groups j that read from i's
 * write support. The intersection of read and write support is used
 * as a projection. Together with a projection of the complement
 * (j's read support minus the intersection) this is used to construct
 * all new values for the read inputs using the join call
 * (join is an intersection operation of sets with different projections, that
 *  can also be supported in MDDs).
 */
void
find_domain_intersections ()
{
    /* Collect write group to read group matrix */
    ci_list *(*group_w2r)[nGrps];
    group_w2r = RTmallocZero (sizeof(*group_w2r) * nGrps);
    //ci_list ***group_w2r = RTmallocZero (sizeof(ci_list *[nGrps*nGrps]) + sizeof(ci_list **[nGrps]));
    writers = RTmallocZero (sizeof(write_group_t[nGrps]));

    rrows = (ci_list**) dm_rows_to_idx_table (read_matrix);
    wrows = (ci_list**) dm_rows_to_idx_table (write_matrix);

    ci_list **rcols = (ci_list**) dm_cols_to_idx_table (read_matrix);
    for (int i = 0; i < nGrps; i++) {
        //group_w2r[i] = (ci_list **) &group_w2r[nGrps + i * nGrps];
        // iterate writing slots s for group i
        for (int *s = ci_begin(w_projs[i]); s < ci_end(w_projs[i]); s++) {
            // iterate groups j reading from s
            for (int *j = ci_begin(rcols[*s]); j < ci_end(rcols[*s]); j++) {
                ci_list *wt = group_w2r[i][*j];
                if (wt == NULL) {
                    writers[i].num_readers++;
                    group_w2r[i][*j] = wt = ci_create (N);
                }
                ci_add (wt, *s);
            }
        }

        // create read support complement sets (for collecting visited states)
        if (ci_count(r_projs[i]) == 0) {
            writers[i].complement = NULL;
        } else {
            ci_list *compl = ci_create (N - ci_count(r_projs[i]));
//            int *s = ci_begin(r_projs[i]);
            for (int l = 0; l < N; l++) {
//                if (s != ci_end(r_projs[l]) && *s == l) {
//                    s++;
//                } else {
                    ci_add_if (compl, l, ci_binary_search(r_projs[i], l) == -1);
//                }
            }
            writers[i].complement = vset_create (domain, compl->count, compl->data);
            HREassert (ci_count(r_projs[i]) + ci_count(compl) == N);
        }
    }
    RTfree (rcols);

    /* Collapse matrix into list ( write_group_t[nGrps] ) */
    for (int i = 0; i < nGrps; i++) {
        int c = 0;
        write_group_t *wg = &writers[i];
        wg->index = i;
        wg->readers = RTmallocZero (sizeof(reader_t[wg->num_readers]));
        for (int j = 0; j < nGrps; j++) {
            ci_list *slots = group_w2r[i][j];
            reader_t *r = &wg->readers[c];
            r->index = j;
            if (slots == NULL) continue;
            c++;

            int compl_len = r_projs[j]->count - slots->count;
            HREassert (compl_len >= 0);
            if (compl_len == 0) continue; // writer's domain overlaps reader

            r->slots = slots;
            r->compl = ci_create (compl_len);
            for (int *s = ci_begin(r_projs[j]); s < ci_end(r_projs[j]); s++)
                ci_add_if (r->compl, *s, ci_binary_search(slots, *s) == -1);
            HREassert(ci_count(r->compl) == compl_len);
            r->complement = vset_create (domain, compl_len, r->compl->data);
            r->tmp = vset_create (domain, slots->count, slots->data);
            //ci_free (slots);
        }
        HREassert (c == wg->num_readers);
    }
    RTfree (group_w2r);

    Printf (infoLong, "\n");
    size_t total = 0;
    for (int j = 0; j < nGrps; j++) {
        for (write_group_t *wg = w_bgn(); wg <  w_end(); wg++) {
            for (reader_t *r = r_bgn(wg); r <  r_end(wg); r++) {
                if (r->index != j) continue;
                if (r->slots == NULL) continue;
                Printf (infoLong, "%2d X %2d -->\t", wg->index, r->index);
                for (int *s = ci_begin(r->slots); s < ci_end(r->slots); s++) {
                    Printf (infoLong, "%2d,", *s);
                    total++;
                }
                Printf (infoLong, "  |  ");
                for (int *s = ci_begin(r->compl); s < ci_end(r->compl); s++) {
                    Printf (infoLong, "%2d,", *s);
                }
                Printf (infoLong, "\n");
            }
        }
        Printf (infoLong, "\n");
    }
    Printf (infoLong, "\nTotal: %zu\n", total);
}

void
init_local (vset_t I)
{
    if (HREme (HREglobal()) == 0) {
        X = vset_create (domain, -1, NULL);
        Q_r = group_tmp;
        V_r = group_explored;
        exact_explored = RTmalloc(nGrps * sizeof(vset_t));
        V_w = RTmalloc(nGrps * sizeof(vset_t));
        Q_w = RTmalloc(nGrps * sizeof(vset_t));
        C_w = RTmalloc(nGrps * sizeof(vset_t));
        X_r = RTmalloc(nGrps * sizeof(vset_t));
        Y_r = RTmalloc(nGrps * sizeof(vset_t));
        N_r = RTmalloc(nGrps * sizeof(vset_t));
        C_r = RTmalloc(nGrps * sizeof(vset_t));
        V_old_r = RTmalloc(nGrps * sizeof(vset_t));

        // TODO: move to projections
        r_compl_projs        = (ci_list **)RTmalloc(sizeof(ci_list *[nGrps]));
        w_compl_projs        = (ci_list **)RTmalloc(sizeof(ci_list *[nGrps]));

        for (int i = 0; i < nGrps; i++) {
            // Store complement sets for read projections
            r_compl_projs[i] = ci_create (N - ci_count(r_projs[i]));
            for (int l = 0; l < N; l++) {
                ci_add_if (r_compl_projs[i], l, ci_binary_search(r_projs[i], l) == -1);
            }

            // Store complement sets for read projections
            w_compl_projs[i] = ci_create (N - ci_count(w_projs[i]));
            for (int l = 0; l < N; l++) {
                ci_add_if (w_compl_projs[i], l, ci_binary_search(w_projs[i], l) == -1);
            }

            exact_explored[i] = vset_create(domain, r_projs[i]->count, r_projs[i]->data);
            vset_copy(exact_explored[i], group_explored[i]);
            V_w[i] = vset_create (domain, w_projs[i]->count, w_projs[i]->data);
            Q_w[i] = vset_create (domain, w_projs[i]->count, w_projs[i]->data);
            C_w[i] = vset_create (domain, w_compl_projs[i]->count, w_compl_projs[i]->data);

            X_r[i] = vset_create (domain, r_projs[i]->count, r_projs[i]->data);
            Y_r[i] = vset_create (domain, r_projs[i]->count, r_projs[i]->data);
            N_r[i] = vset_create (domain, r_projs[i]->count, r_projs[i]->data);
            C_r[i] = vset_create (domain, r_compl_projs[i]->count, r_compl_projs[i]->data);
            V_old_r[i] = vset_create (domain, r_projs[i]->count, r_projs[i]->data);

            vset_project (Q_r[i], I);       // init read queue

            vset_copy    (V_r[i], Q_r[i]);  // todo: if no chaining?
            vset_copy    (N_r[i], Q_r[i]);
            vset_project (V_w[i], I);       // init write visited

            vset_project(C_r[i], I);
            vset_project(C_w[i], I);



        }

        source_set = vset_create(domain, -1, NULL);
        image_set = vset_create(domain, -1, NULL);

        p_all = ci_create (N);
        for (int l = 0; l < N; l++) ci_set (p_all, l, l);

        find_domain_intersections ();


    }



    HREbarrier (HREglobal());
}

void
deinit_local ()
{
    if (HREme (HREglobal()) == 0) {
        vset_destroy (X);
        for (int i = 0; i < nGrps; i++) {
            vset_destroy (V_w[i]);
            vset_destroy (Q_w[i]);
            vset_destroy (X_r[i]);
            vset_destroy (Y_r[i]);
        }
        RTfree (V_w);
        RTfree (Q_w);
        RTfree (X_r);
        RTfree (Y_r);

        ci_free (p_all);

        for (write_group_t *wg = w_bgn(); wg <  w_end(); wg++) {
            for (reader_t *r = r_bgn(wg); r <  r_end(wg); r++) {
                if (r->compl)       ci_free (r->compl);
                if (r->slots)       ci_free (r->slots);
                if (r->complement)  vset_destroy (r->complement);
                if (r->tmp)         vset_destroy (r->tmp);
            }
            RTfree (wg->readers);
            vset_destroy (wg->complement);
        }
        RTfree (writers);

        find_domain_intersections ();
    }
    HREbarrier (HREglobal());
}

void
print_local (vset_t V, int level)
{
    RTprintTimer (info, reach_timer, "Local reach took");
    long int n;
    double e;
    vset_count (V, &n, &e);
    Warning (info, "Local Levels: %d  %.0f", level, e);
}

void
run_local (vset_t I, vset_t V)
{
    for (int i = 0; i < nGrps; i++) {
        vset_count_info(group_explored[i], i, 0);
    }


    Warning (info, "Localized [0]");

    init_local (I);

    int level;

    RTstartTimer(reach_timer);
    if (sat_strategy == SAT) {
        level = reach_local_sat(I, V);
    } else {
        level = reach_local (I, V);
    }

    RTstopTimer(reach_timer);

    print_local (V, level);

    deinit_local ();

    final_final_stats_reporting ();

    RTresetTimer(reach_timer);
}



