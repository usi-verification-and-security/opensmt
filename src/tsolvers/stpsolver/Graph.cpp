#include "Graph.hpp"

void Graph::addVertex(PTRef x) {
    if (!vertices.count(x))
        vertices[x] = Vertex();
}

// append a new edge constraint to graph
bool Graph::addEdge(const Edge &e, const opensmt::Number &cost) {
    // for detecting negative cycles, we need to care only about the lowest cost edge between two vertices
    if (!edges.count(e))
        vertices[e.from].neighbours.push_back(e.to);
    if (!edges.count(e) || cost < edges[e]) {
        edges[e] = cost;
        added.push_back(e);
    }
    return true;
}

bool Graph::check() {
    // TODO: replace with more efficient structures
    std::map<PTRef, opensmt::Number> phi;       // lower bound on how much potential must change
    std::map<PTRef, opensmt::Number> updated;   // new potential function
    for (const auto & i : added) {
        phi[i.to] = vertices[i.from].value + edges[i] - vertices[i.to].value;
    }

    for (PTRef s = getArgMin(phi); phi[s] < 0 && areAddedZero(phi); s = getArgMin(phi)) {
        updated[s] = vertices[s].value + phi[s];
        phi[s] = 0;

        for (const auto &t : vertices[s].neighbours)
            if (updated[t] == vertices[t].value)
                phi[t] = std::min(phi[t], updated[s] + edges[Edge(s,t)] - vertices[t].value);
    }

    if (!areAddedZero(phi)) {
        added.clear();
        return false;
    }

    for (const auto &i : updated)
        vertices[i.first].value = i.second;

    added.clear();
    return true;
}


// finds argmin in linear time
// TODO: replace with faster data structure
PTRef Graph::getArgMin(const std::map<PTRef, opensmt::Number> &func) const {
    auto argmin = func.begin()->first;  // func always has at least one element (checked in check())
    auto min = func.at(argmin);
    for (const auto &x : func)
        if (x.second < min) {
            argmin = x.first;
            min = x.second;
        }
    return argmin;
}

// check phi[e.from] of all added edges is 0 (or non-existent). Otherwise a negative cycle exists.
bool Graph::areAddedZero(const std::map<PTRef, opensmt::Number> &phi) const {
    for (const auto &i : added)
        if (phi.count(i.from) && phi.at(i.from) != 0) return false;

    return true;
}