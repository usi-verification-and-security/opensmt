#ifndef OPENSMT_STPSTORE_C
#define OPENSMT_STPSTORE_C

#include "STPStore.h"

template<class T>
VertexRef STPStore<T>::createVertex() {
    return VertexRef{vertices++};
}

template<class T>
EdgeRef STPStore<T>::createEdge(VertexRef from, VertexRef to, T cost) {
    uint32_t i = edges.size();
    EdgeRef r{i};
    edges.emplace_back(from, to, EdgeRef_Undef, cost, 0);
    return r;
}

template<class T>
void STPStore<T>::setNegation(EdgeRef a, EdgeRef b) {
    edges[a.x].neg = b;
    edges[b.x].neg = a;
}

template<class T>
void STPStore<T>::clear() {
    edges.clear();
    vertices = 1;   // clear all vertices except zero
}

#endif //OPENSMT_STPSTORE_C
