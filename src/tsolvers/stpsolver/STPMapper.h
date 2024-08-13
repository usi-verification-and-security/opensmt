#ifndef OPENSMT_STPMAPPER_H
#define OPENSMT_STPMAPPER_H

#include "STPStore.h"
// implementations of template functions #included below class definition

#include <logics/ArithLogic.h>
#include <pterms/Pterm.h>

#include <vector>

namespace opensmt {
template<class T>
class STPMapper {
public:
    STPMapper(ArithLogic const & l, STPStore<T> const & s);

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

    std::vector<EdgeRef> const & edgesOf(VertexRef v) { return edgesContainingVert[v.x]; }

    void clear();

private:
    ArithLogic const & logic;

    STPStore<T> const & store;

    std::vector<PTRef> vertRefToVar;                       // maps VertRefs to variables' PTRefs
    std::vector<VertexRef> varToVertRef;                   // maps PTRefs of variables to VertRefs
    std::vector<EdgeRef> leqToEdgeRef;                     // maps PTRefs of inequalities to EdgeRefs
    std::vector<PTRef> edgeRefToLeq;                       // reverse of leqToEdgeRef
    std::vector<PtAsgn> edgeRefToAsgn;                     // maps assigned edges to assignments that set them
    std::vector<std::vector<EdgeRef>> edgesContainingVert; // list of edges each vertex appears in
};
} // namespace opensmt

#include "STPMapper_implementations.hpp"

#endif // OPENSMT_STPMAPPER_H
