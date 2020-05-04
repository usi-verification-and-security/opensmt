#include "STPEdgeGraph.h"

bool STPEdgeGraph::isTrue(EdgeRef e) {
    return assigned.size() > e.x && assigned[e.x];
}

void STPEdgeGraph::setTrue(EdgeRef e) {
    if (assigned.size() <= e.x)
        assigned.resize(e.x + 1, false);
    assigned[e.x] = true;
}