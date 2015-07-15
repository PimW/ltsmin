#include <hre/config.h>

#include <mc-lib/renault-unionfind.h>

#include <mc-lib/atomics.h>

typedef enum r_uf_status_e {
    r_UF_UNSEEN     = 0, // initial
    r_UF_INIT       = 1,
    r_UF_LIVE       = 2,
    r_UF_LOCKED     = 3,
    r_UF_DEAD       = 4
} r_uf_status;

struct r_uf_node_s {
    ref_t           parent;                 // The parent in the UF tree
    unsigned char   rank;                   // The height of the UF tree
    unsigned char   r_uf_status;              // {UNSEEN, INIT, LIVE, LOCKED, DEAD}
};

typedef struct r_uf_node_s r_uf_node_t;

struct r_uf_s {
    r_uf_node_t      *array;   // array: [ref_t] -> uf_node
};

r_uf_t *
r_uf_create ()
{
    //HREassert (sizeof(sz_w)*8 >= W, "Too many workers for the current structure; please redefine sz_w to a larger size");
    r_uf_t         *uf = RTmalloc (sizeof(r_uf_t));
    uf->array          = RTmallocZero ( sizeof(r_uf_node_t) * (1ULL << dbs_size) );
    return uf;
}

// successor handling

char     
r_uf_make_claim (const r_uf_t* uf, ref_t state)
{
    // Is the state unseen? ==> Initialize it
    if (cas(&uf->array[state].r_uf_status, r_UF_UNSEEN, r_UF_INIT)) {
        // create state and add worker

        atomic_write (&uf->array[state].parent, state);
        atomic_write (&uf->array[state].r_uf_status, r_UF_LIVE);

        return CLAIM_FIRST;
    }

    // Is someone currently initializing the state?
    while (atomic_read (&uf->array[state].r_uf_status) == r_UF_INIT);

    // Is the state dead?
    if (r_uf_is_dead(uf, state))
        return CLAIM_DEAD;
    else 
        return CLAIM_SUCCESS;
}

ref_t
r_uf_find (const r_uf_t* uf, ref_t state)
{
    // recursively find and update the parent (path compression)
    ref_t parent = atomic_read(&uf->array[state].parent);
    if (parent == state)
        return parent;
    ref_t root = r_uf_find (uf, parent);
    if (root != parent)
        atomic_write(&uf->array[state].parent, root);
    return root;
}
/*
ref_t
r_uf_waitfree_find (const uf_t* uf, ref_t state) // wait-free uf impl.
{
    ref_t x = state;
    ref_t y = state;
    ref_t parent = atomic_read(&uf->array[x].parent);
    
    while (x != parent) {
        x = parent;
        parent = atomic_read(&uf->array[x].parent);
    }

    while (uf->array[y].rank < uf->array[x].rank) {
        parent = atomic_read(&uf->array[y].parent);
        cas(&uf->array[y].parent, parent, x);
        y = parent;
    }

    return x;
}

bool
r_uf_waitfree_sameset (const r_uf_t* uf, ref_t state_x, ref_t state_y)
{
    ref_t x = state_x;
    ref_t y = state_y;

    while (1) {
        x = r_uf_waitfree_find (uf, x);
        y = r_uf_waitfree_find (uf, y);

        if (x == y) return true;
        if (atomic_read(&uf->array[x].parent) != x) return false;

    }
}*/

bool
r_uf_sameset (const r_uf_t* uf, ref_t state_x, ref_t state_y)
{
retry:{
    // TODO check if correct
    ref_t x_f = r_uf_find(uf, state_x);
    ref_t y_f = r_uf_find(uf, state_y);

    // x_f may change during find(y), 
    // - if so, try again
    // - otherwise, x_f is unchanged after finding y_f => sameset holds
    ref_t x_p = atomic_read(&uf->array[x_f].parent);
    ref_t y_p = atomic_read(&uf->array[y_f].parent); // should not be needed

    if ( x_f != x_p || y_f != y_p) {
        // if parent got updated, try again
        state_x = x_p;
        state_y = y_p;
        goto retry;
    }

    return x_f == y_f;
}}

void
r_uf_union (const r_uf_t* uf, ref_t state_x, ref_t state_y)
{
    bool result     = false;
    ref_t x_f, y_f, root, other;


    while (!result) {
        x_f = r_uf_find(uf, state_x);
        y_f = r_uf_find(uf, state_y);

        if (x_f == y_f) return; // SameSet(x,y)

        root  = x_f;
        other = y_f;

        // swap(root,other) if root.rank < other.rank
        if (uf->array[x_f].rank < uf->array[y_f].rank) { 
            root  = y_f;
            other = x_f;
        } 

        // set other.parent = root
        result = cas(&uf->array[other].parent, other, root);
        if (uf->array[root].parent != root) result = false;
        if (!result) continue;

        // increment the rank if it is equal
        if (uf->array[root].rank == uf->array[other].rank) {
            uf->array[root].rank ++;
        }
    }
}


// dead

bool
r_uf_mark_dead (const r_uf_t* uf, ref_t state) 
{
    // returns if it has marked the state dead
    bool result = false;

    ref_t f = r_uf_find(uf, state); 

    while (!r_uf_is_dead(uf, f)) {
        f = r_uf_find(uf, f); 

        char tmp = atomic_read (&uf->array[f].r_uf_status);
        if (tmp != r_UF_DEAD) {
            result = cas(&uf->array[f].r_uf_status, tmp, r_UF_DEAD);
        }
    }


    //HREassert (r_uf_is_dead(uf, state), "state should be dead");

    return result;
}

bool
r_uf_is_dead (const r_uf_t* uf, ref_t state)
{
    if (atomic_read(&uf->array[state].r_uf_status) == r_UF_UNSEEN ||
        atomic_read(&uf->array[state].r_uf_status) == r_UF_INIT) 
        return false;
    ref_t f = r_uf_find(uf, state); 
    return atomic_read(&uf->array[f].r_uf_status) == r_UF_DEAD;
}


// locking

ref_t      
r_uf_lock (const r_uf_t* uf, ref_t state_x, ref_t state_y)
{
    ref_t a = state_x;
    ref_t b = state_y;
    while (1) {
        a = r_uf_find(uf, state_x);
        b = r_uf_find(uf, state_y);

        // SameSet(a,b)
        if (a == b) {
            return false;
        }   

        if (a > b) { // SWAP(a,b)
            ref_t tmp = a;
            a = b;
            b = tmp;
        }

        // lock smallest ref first
        if (cas(&uf->array[a].r_uf_status, r_UF_LIVE, r_UF_LOCKED)) {
            if (atomic_read(&uf->array[a].parent) == a) {
                // a is successfully locked
                if (cas(&uf->array[b].r_uf_status, r_UF_LIVE, r_UF_LOCKED)) {
                    if (atomic_read(&uf->array[b].parent) == b) {
                        // b is successfully locked
                        return true;
                    } 
                    atomic_write (&uf->array[b].r_uf_status, r_UF_LIVE);
                } 
            } 
            atomic_write (&uf->array[a].r_uf_status, r_UF_LIVE);
        }
    }
}

void      
r_uf_unlock (const r_uf_t* uf, ref_t state)
{
    HREassert(uf->array[state].r_uf_status == r_UF_LOCKED)
    atomic_write (&uf->array[state].r_uf_status, r_UF_LIVE);
}

// testing

bool
r_uf_mark_undead (const r_uf_t* uf, ref_t state) 
{
    // only used for testing

    bool result = 0;

    ref_t f = r_uf_find(uf, state); 

    result = cas(&uf->array[f].r_uf_status, r_UF_DEAD, r_UF_LIVE);

    return result;
}

void         
r_uf_debug (const r_uf_t* uf, ref_t state) 
{ 
    Warning(info, "state:  %zu\t, parent: %zu\t, rank:   %d\t, status: %d\t",
        state, 
        uf->array[state].parent,  
        uf->array[state].rank,  
        uf->array[state].r_uf_status);
    if (uf->array[state].parent != state) {
        r_uf_debug (uf, uf->array[state].parent); 
    }
}

void         
r_uf_free (r_uf_t* uf)
{
    RTfree(uf->array);
    RTfree(uf);
}