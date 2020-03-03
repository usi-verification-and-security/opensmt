#ifndef OPENSMT_GRAPH_HPP
#define OPENSMT_GRAPH_HPP


#include <PTRef.h>
#include <map>
#include <PtStructs.h>
#include <vector>

// describes the type of known edge
enum class e_type : char {
    unassigned = 0,
    assigned,
    propagated, // assigned & all consequences found
    consequence // provable from assigned (propagated) edges
};

struct Edge {
    PTRef from, to;
    int cost;
};

struct Vertex {
    int value;
    std::vector<Edge> neighbours; // all edges coming from this vertex
};

class Graph {
    std::map<PTRef, Vertex> vertices;
    std::map<Edge, e_type> edges;
    PTRef GetArgMin(std::map<PTRef, int> func);
public:
    void AddVertex(PTRef x);
    bool AddEdge(Edge e);
};


#endif //OPENSMT_GRAPH_HPP
