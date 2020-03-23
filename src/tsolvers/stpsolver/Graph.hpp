#ifndef OPENSMT_GRAPH_HPP
#define OPENSMT_GRAPH_HPP


#include <PTRef.h>
#include <map>
#include <PtStructs.h>
#include <vector>
#include <Number.h>

struct Edge {
    PTRef from, to;
    // Temporary workaround to be able to use as map keys
    // Shouldn't be needed once better data structures are used
    Edge() = default;
    Edge(PTRef from, PTRef to) : from(from), to(to)
    {}

    bool operator <(const Edge & other) const {
        return from < other.from || to < other.to;
    }
    bool operator ==(const Edge & other) const {
        return from == other.from && to == other.to;
    }
};

struct Vertex {
    opensmt::Number value;
    std::vector<PTRef> neighbours; // all edges coming from this vertex
};

class Graph {
    std::map<PTRef, Vertex> vertices;
    std::map<Edge, opensmt::Number> edges; // assigned edges and their costs
    std::vector<Edge> added;
    PTRef getArgMin(const std::map<PTRef, opensmt::Number> &func) const;
    bool areAddedZero(const std::map<PTRef, opensmt::Number> &phi) const;
public:
    void addVertex(PTRef x);
    bool addEdge(const Edge& e, const opensmt::Number &cost);
    bool check();
};


#endif //OPENSMT_GRAPH_HPP
