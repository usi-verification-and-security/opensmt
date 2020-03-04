#include "Graph.hpp"

void Graph::addVertex(PTRef x) {
    vertices[x] = Vertex();
}

// append a new edge constraint to graph
bool Graph::addEdge(const Edge& e) {
    if (edges.count(e) && edges.at(e) == e_type::consequence)
        return true;

    edges[e] = e_type::assigned;

    // horribly inefficient. used as proof of concept.
    // will be replaced later
    std::map<PTRef, opensmt::Number> phi;
    std::map<PTRef, opensmt::Number> updated;

    //initial setup;
    for (const auto & i : vertices)
       phi[i.first] = 0;
    phi[e.to] = vertices[e.from].value + e.cost - vertices[e.to].value;

    // main loop of algorithm
    for (PTRef s = getArgMin(phi); phi[s] < 0 && phi[e.from] == 0; s = getArgMin(phi)) {
        // update value of s by phi
        updated[s] = vertices[s].value + phi[s];
        phi[s] = 0;
        // update changeability of all neighbours
        for (const auto & t : vertices[s].neighbours)
            if (updated[t.to] == vertices[t.to].value)
                phi[t.to] = std::min(phi[t.to], updated[s] + t.cost - vertices[t.to].value);
    }

    // negative cycle detected
    if (phi[e.from] < 0)
        return false;

    for (const auto & i : updated) {
        vertices[i.first].value = i.second;
    }

    return true;
}

// finds argmin in linear time
// TODO: replace with faster data structure
PTRef Graph::getArgMin(std::map<PTRef, opensmt::Number> func) {
    PTRef min = func.begin()->first;
    for (const auto & x : func)
        if (x.first < min) min = x.first;

    return min;
}
