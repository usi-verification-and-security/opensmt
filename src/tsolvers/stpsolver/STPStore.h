#ifndef OPENSMT_STPSTORE_H
#define OPENSMT_STPSTORE_H

#include <cstdint>
#include <vector>
#include <Number.h>

struct VertexRef {
    uint32_t x;
    inline bool operator==(VertexRef other) const { return x == other.x; }
    explicit operator bool() const { return x != INT32_MAX; }
};

struct EdgeRef {
    uint32_t x;
    inline bool operator==(EdgeRef other) const { return x == other.x; }
    explicit operator bool() const { return x != INT32_MAX; }
};

struct Edge {
    VertexRef from, to;
    EdgeRef neg;
    opensmt::Number cost;
};

class STPStore {
private:
    std::vector<VertexRef> verts;           // list of all created vertices
    std::vector<Edge> edges;                //                     edges

    // vertices and edges have separate Ref types to avoid long gaps in the lists below
    using AdjList = std::vector<EdgeRef>;
    std::vector<AdjList> incoming;          // for each vertex, list of edges ending in that vertex
    std::vector<AdjList> outgoing;          //                               starting
public:
    VertexRef createVertex();
    EdgeRef createEdge(VertexRef from, VertexRef to, opensmt::Number cost);

    size_t vertexNum() const  { return verts.size(); }
    size_t edgeNum() const { return edges.size(); }
    Edge & getEdge(EdgeRef e) { return edges[e.x]; }
    void setNegation(EdgeRef a, EdgeRef b);
    EdgeRef hasNeighbour(VertexRef from, VertexRef to);
};

static VertexRef VertRef_Undef = VertexRef { INT32_MAX };
static EdgeRef EdgeRef_Undef = EdgeRef { INT32_MAX };
#endif //OPENSMT_STPSTORE_H
