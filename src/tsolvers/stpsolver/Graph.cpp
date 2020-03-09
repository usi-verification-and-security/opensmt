#include "Graph.hpp"

Graph::Graph() noexcept : valid(true) {}

void Graph::addVertex(PTRef x) {
    if (!vertices.count(x))
        vertices[x] = Vertex();
}

// FIXME: performs consistency check when adding
// append a new edge constraint to graph
bool Graph::addEdge(const Edge& e) {
    if (edges.count(e)) return true;

    edges[e] = e_type::assigned;
    vertices[e.from].neighbours.push_back(e);
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
    if (phi[e.from] < 0) {
        valid = false;
        vertices[e.from].neighbours.pop_back();
    }
    else {
        for (const auto & i : updated) {
            vertices[i.first].value = i.second;
        }
    }

    return true;
}

bool Graph::check() {
    return valid;
}


// finds argmin in linear time
// TODO: replace with faster data structure
PTRef Graph::getArgMin(std::map<PTRef, opensmt::Number> func) {
    auto argmin = func.begin()->first;
    auto min = func[argmin];
    for (const auto &x : func)
        if (x.second < min) {
            argmin = x.first;
            min = x.second;
        }
    return argmin;
}
