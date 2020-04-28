#include <Pterm.h>
#include "STPMapper.h"

void STPMapper::setVert(PTRef var, VertexRef vert) {
    uint32_t idx = Idx(logic.getPterm(var).getId());
    if (varToVertRef.size() <= idx)
        varToVertRef.resize(idx + 1, VertRef_Undef);

    varToVertRef[idx] = vert;
}

void STPMapper::setEdge(PTRef leq, EdgeRef edge) {
   uint32_t idx = Idx(logic.getPterm(leq).getId());
   if (leqToEdgeRef.size() <= idx)
       leqToEdgeRef.resize(idx + 1, EdgeRef_Undef);

   leqToEdgeRef[idx] = edge;
}