#ifndef OPENSMT_STPSTORE_H
#define OPENSMT_STPSTORE_H

#include <cstdint>
#include <vector>
#include <Number.h>
#include <SolverTypes.h>
#include <PtStructs.h>

struct VertexRef {
    uint32_t x;
    inline bool operator==(VertexRef other) const { return x == other.x; }
    inline bool operator!=(VertexRef other) const { return x != other.x; }
};

struct EdgeRef {
    uint32_t x;
    inline bool operator==(EdgeRef other) const { return x == other.x; }
    inline bool operator!=(EdgeRef other) const { return x != other.x; }
};

static VertexRef VertRef_Undef = VertexRef { INT32_MAX };
static EdgeRef EdgeRef_Undef = EdgeRef { INT32_MAX };

struct Edge {
    VertexRef from, to;     // vertices of this edge
    EdgeRef neg;            // the logical negation of this edge
    ptrdiff_t cost;   // cost of this edge

    uint32_t setTime;       // timestamp of when this was assigned as true (0 if it wasn't assigned)
    PtAsgn asgn;            // assignment that caused this edge to be set (for actually set edges and not consequences)
};

class STPStore {
private:
    uint32_t vertices;                  // number of created vertices (a vertex doesn't actually carry any information)
    std::vector<Edge> edges;            // list of all created edges
public:
    STPStore() : vertices(0) {}
    VertexRef createVertex();
    EdgeRef createEdge(VertexRef from, VertexRef to, ptrdiff_t cost);

    size_t vertexNum() const  { return vertices; }
    size_t edgeNum() const { return edges.size(); }
    Edge & getEdge(EdgeRef e) { return edges[e.x]; }
    void setNegation(EdgeRef a, EdgeRef b);
    void clear();
};

#endif //OPENSMT_STPSTORE_H
