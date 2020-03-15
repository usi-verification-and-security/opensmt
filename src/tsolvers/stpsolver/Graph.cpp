#include "Graph.hpp"

Graph::Graph() noexcept : valid(true) {}

void Graph::addVertex(PTRef x) {
    if (!vertices.count(x))
        vertices[x] = Vertex();
}

// append a new edge constraint to graph
bool Graph::addEdge(const Edge& e) {
    if (edges.count(e)) return true;

    edges[e] = e_type::assigned;
    vertices[e.from].neighbours.push_back(e);
    added.push_back(e);
    return true;
}

bool Graph::check() {
    if (!valid) return valid;
    if (added.empty()) return valid;

    // TODO: replace with more efficient structures
    std::map<PTRef, opensmt::Number> phi;       // estimate on how much potential can change
    std::map<PTRef, opensmt::Number> updated;   // new potential function
    for (const auto & i : added) {
        phi[i.to] = vertices[i.from].value + i.cost - vertices[i.to].value;
    }

    for (PTRef s = getArgMin(phi); phi[s] < 0 && areAddedZero(phi); s = getArgMin(phi)) {
        updated[s] = vertices[s].value + phi[s];
        phi[s] = 0;

        for (const auto &t : vertices[s].neighbours)
            if (updated[t.to] == vertices[t.to].value)
                phi[t.to] = std::min(phi[t.to], updated[s] + t.cost - vertices[t.to].value);
    }

    if (!areAddedZero(phi))
        valid = false;
    else
        for (const auto &i : updated)
            vertices[i.first].value = i.second;

    added.clear();
    return valid;
}


// finds argmin in linear time
// TODO: replace with faster data structure
PTRef Graph::getArgMin(std::map<PTRef, opensmt::Number> func) {
    auto argmin = func.begin()->first;  // func always has at least one element (checked in check())
    auto min = func[argmin];
    for (const auto &x : func)
        if (x.second < min) {
            argmin = x.first;
            min = x.second;
        }
    return argmin;
}

// check phi[e.from] of all added edges is 0 (or non-existent). Otherwise a negative cycle exists.
bool Graph::areAddedZero(std::map<PTRef, opensmt::Number> phi) {
    for (const auto &i : added)
        if (phi.count(i.from) && phi[i.from] != 0) return false;

    return true;
}