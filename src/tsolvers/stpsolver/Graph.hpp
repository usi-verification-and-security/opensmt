#ifndef OPENSMT_GRAPH_HPP
#define OPENSMT_GRAPH_HPP


#include <PTRef.h>
#include <map>
#include <PtStructs.h>
#include <vector>
#include <Number.h>

// describes the type of known edge
enum class e_type : char {
    unassigned = 0,
    assigned,
    propagated, // assigned & all consequences found
    consequence // provable from assigned (propagated) edges
};

struct Edge {
    PTRef from, to;
    opensmt::Number cost;
};

struct Vertex {
    opensmt::Number value;
    std::vector<Edge> neighbours; // all edges coming from this vertex
};

class Graph {
    std::map<PTRef, Vertex> vertices;
    std::map<Edge, e_type> edges;
    PTRef getArgMin(std::map<PTRef, opensmt::Number> func);
public:
    void addVertex(PTRef x);
    bool addEdge(const Edge& e);
};


#endif //OPENSMT_GRAPH_HPP
