#ifndef ALG_REVPDR_H
#define ALG_REVPDR_H

#include <vset-lib/vector_set.h>

extern bool pdr(vset_t I, vset_t P, vset_t universe);
extern bool reverse_reach(vset_t I, vset_t P, vset_t U);

#endif //ALG_SCC_H