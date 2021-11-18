#ifndef OPENSMT_STPMAPPER_H
#define OPENSMT_STPMAPPER_H

#include <vector>
#include "ArithLogic.h"
#include <Pterm.h>
#include "STPStore.h"
// implementations of template functions #included below class definition

template<class T>
class STPMapper {
private:
    const ArithLogic &logic;

    const STPStore<T> &store;

    std::vector<PTRef> vertRefToVar;                        // maps VertRefs to variables' PTRefs
    std::vector<VertexRef> varToVertRef;                    // maps PTRefs of variables to VertRefs
    std::vector<EdgeRef> leqToEdgeRef;                      // maps PTRefs of inequalities to EdgeRefs
    std::vector<PTRef> edgeRefToLeq;                        // reverse of leqToEdgeRef
    std::vector<PtAsgn> edgeRefToAsgn;                      // maps assigned edges to assignments that set them
    std::vector<std::vector<EdgeRef>> edgesContainingVert;  // list of edges each vertex appears in

public:
    STPMapper(const ArithLogic &l, const STPStore<T> &s);

    void setVert(PTRef var, VertexRef vert);

    void registerEdge(EdgeRef edge);

    void mapEdge(PTRef leq, EdgeRef edge);

    void setAssignment(EdgeRef edge, PtAsgn asgn);

    void removeAssignment(EdgeRef edge);

    PtAsgn getAssignment(EdgeRef edge) const;

    PTRef getPTRef(VertexRef var) const;

    VertexRef getVertRef(PTRef var) const;

    EdgeRef getEdgeRef(PTRef leq) const;

    EdgeRef getEdgeRef(VertexRef y, VertexRef x, T c) const;

    PTRef getPTRef(EdgeRef edge) const;

    const std::vector<EdgeRef> &edgesOf(VertexRef v) { return edgesContainingVert[v.x]; }

    void clear();
};

#include "STPMapper_implementations.hpp"

#endif //OPENSMT_STPMAPPER_H
