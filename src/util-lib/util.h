#ifndef UTIL_LTSMIN_H
#define UTIL_LTSMIN_H

#include <stdbool.h>
#include <stdint.h>
#include <hre/user.h>
#include <assert.h>

#define max(a,b) ({ \
    typeof(a) _a = (a); \
    typeof(b) _b = (b); \
    _a > _b ? _a : _b; \
})

#define min(a,b) ({ \
    typeof(a) _a = (a); \
    typeof(b) _b = (b); \
    _a < _b ? _a : _b; \
})

#define swap(a,b) ({ \
    typeof(a) tmp = a; \
    a = b; \
    b = tmp; \
})

/**
 * ci = count, integer
 */
typedef struct ci_list
{
    int count;
    int data[];
} ci_list;

extern ci_list *ci_create (size_t size);

extern void ci_free (ci_list *list);

extern void ci_print (ci_list *list);

extern void ci_debug (ci_list *list);

extern void ci_sort (ci_list *list);

static inline int
ci_get (ci_list *list, int index)
{
    return list->data[index];
}

static inline void
ci_set (ci_list *list, int index, int val)
{
    list->data[index] = val;
}

/* begin iterator */
static inline int *
ci_begin (ci_list *list)
{
    return &list->data[0];
}

static inline int *
ci_end (ci_list *list)
{
    return &list->data[list->count];
}
/* end iterator */

static inline int
ci_top (ci_list *list)
{
    HREassert(list->count >= 0);
    return list->data[list->count - 1];
}

static inline int
ci_pop (ci_list *list)
{
    HREassert(list->count >= 0);
    return list->data[--list->count];
}

static inline int
ci_find (ci_list *list, int e)
{
    for (int *a = ci_begin(list); a != ci_end(list); a++)
         if (*a == e) return a - ci_begin(list);
    return -1;
}

static inline int
ci_count (ci_list *list)
{
    return list->count;
}

static inline void
ci_clear (ci_list *list)
{
    list->count = 0;
}

static inline void
ci_add (ci_list *list, int num)
{
    list->data[list->count++] = num;
}

/**
 * Remove element from array based on index, assumes all elements are unique.
 * Resizes the array. (does not de-allocate memory)
 * @param list
 * @param index
 */
static inline void
ci_remove(ci_list *list, int num)
{
    for (int a = num; a != list->count; a++) {
        list->data[a] = list->data[a+1];
    }
    list->count--; // resize
}

static inline int
ci_binary_search (ci_list *list, int key)
{
    int             imin = 0;
    int             imax = list->count - 1;
    while (imax >= imin) {
        int imid = imin + ((imax - imin) >> 1);
        if (list->data[imid] == key) {
            return imid;
        } else if (list->data[imid] < key) {
            imin = imid + 1;
        } else {
            imax = imid - 1;
        }
    }
    return -1;
}

static inline void
ci_add_if (ci_list *list, int num, int condition)
{
    list->data[list->count] = num;
    list->count += condition != 0;
}

static inline void
ci_copy(ci_list *dst, ci_list *src)
{
    //assert(dst->count >= src->count); // make sure we only write to allocated memory

    ci_clear(dst);

    for (int i = 0; i < src->count; i++) {
        ci_add(dst, src->data[i]);
    }

    assert(dst->count == src->count);
}

/**
 * An inefficient implementation of union on ci_lists it just adds all indices
 * that don't exist yet and then sorts the resulting array.
 *
 * Example:
 *  input: dst = [1, 3, 5] and src = [2, 4]
 *  output: dst = [1, 2, 3, 4, 5]
 *
 * @param dst
 * @param src
 */
static inline void
ci_union(ci_list *dst, ci_list *src)
{
    for (int *s = ci_begin(src); s < ci_end(src); s++) {
        ci_add_if (dst, *s, ci_find(dst, *s) == -1);
    }
    ci_sort(dst);
}

/**
 * Executes an array minus and removes values in src from dst.
 * Assumes both arrays are unique and don't contain duplicate values
 *
 * Example:
 *  input: dst = [1, 2, 3, 5] and src = [2, 4, 5]
 *  output: dst = [1, 3]
 *
 * @param dst
 * @param src
 */
static inline void
ci_minus(ci_list *dst, ci_list *src)
{
    int i = 0;
    int j = 0;

    while (i < dst->count && j < src->count) {
        if (dst->data[i] < src->data[j]) {
            i++;
        } else if (dst->data[i] > src->data[j]) {
            j++;
        } else { // dst->data[i] == src->data[j]
            ci_remove(dst, i); // removes index and shrinks array
            j++; // assuming all values are unique we don't have to check twice
        }
    }
}

/**
 * Creates an inverted list for src, based on base.
 * This requires src<=base and dst.count = base.count - src.count
 *
 * Example:
 *  Input: src =  [1, 3, 5] and base = [1, 2, 3, 4, 5]
 *  Output: dst = [2, 4]
 *
 * @param dst
 * @param src
 * @param base
 */
static inline void
ci_invert(ci_list *dst, ci_list *src, ci_list *base)
{
    ci_clear(dst);
    for (int *a = ci_begin(base); a != ci_end(base); a++) {
        ci_add_if(dst, *a, ci_binary_search(src, *a) == -1);
    }
    ci_sort(dst);
}

static inline void
list_invert (ci_list *list)
{
    for (int i = 0; i < list->count / 2; i++) {
        swap (list->data[i], list->data[list->count - i - 1]);
    }
}



extern char *gnu_basename (char *path);

extern bool has_suffix(const char *str, const char *suffix);

extern bool has_prefix (const char *name, const char *prefix);

extern void randperm (int *perm, int n, uint32_t seed);

extern int char_array_search (char *args[], int length, char *key);

extern void strtoupper (char *str, char *out, size_t outlen);

extern char *strupper(char *str);

static inline size_t
INT_SIZE (size_t size)
{
    return (size + 3) / 4;
}

extern int long_mult_overflow(const long si_a, const long si_b);

#endif // UTIL_LTSMIN_H

