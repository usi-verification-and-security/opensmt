#ifndef OPENSMT_STPMAPPER_H
#define OPENSMT_STPMAPPER_H

#include <vector>
#include <LALogic.h>
#include <Pterm.h>
#include "STPStore.h"


class STPMapper {
    const LALogic &logic;

    const STPStore &store;

    vec<VertexRef> varToVertRef;                    // maps PTRefs of variables to VertRefs
    vec<EdgeRef> leqToEdgeRef;                      // maps PTRefs of inequalities to EdgeRefs
    vec<PTRef> edgeRefToLeq;                        // reverse of leqToEdgeRef
    vec<PtAsgn> edgeRefToAsgn;                      // maps assigned edges to assignments that set them
    vec<vec<EdgeRef>> edgesContainingVert;          // list of edges each vertex appears in

public:
    STPMapper(const LALogic &l, const STPStore &s);
    void setVert(PTRef var, VertexRef vert);
    void registerEdge(EdgeRef edge);
    void mapEdge(PTRef leq, EdgeRef edge);
    void setAssignment(EdgeRef edge, PtAsgn asgn);
    void removeAssignment(EdgeRef edge);
    PtAsgn getAssignment(EdgeRef edge) const;
    VertexRef getVertRef(PTRef var) const;
    EdgeRef getEdgeRef(PTRef leq) const;
    EdgeRef getEdgeRef(VertexRef y, VertexRef x, SafeInt c) const;
    PTRef getPTRef(EdgeRef edge) const;
    const vec<EdgeRef> & edgesOf(VertexRef v) { return edgesContainingVert[v.x]; }
    void clear();
};

#endif //OPENSMT_STPMAPPER_H
