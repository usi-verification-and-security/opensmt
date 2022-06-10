/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_SCOPEDVECTOR_H
#define OPENSMT_SCOPEDVECTOR_H

#include <vector>

namespace opensmt {

template<typename T>
class ScopedVector {
    std::vector<T> elements;
    std::vector<unsigned> limits;

public:
    void push(T const & element) { return elements.push_back(element); }

    void pushScope() { limits.push_back(elements.size()); }

    void popScope();

    template<typename TFun>
    void popScope(TFun callback);
};

template<typename T>
void ScopedVector<T>::popScope() {
    popScope([](){});
}

template<typename T>
template<typename TFun>
void ScopedVector<T>::popScope(TFun callback) {
    assert(not limits.empty());
    auto lastLimit = limits.back();
    limits.pop_back();
    assert(elements.size() >= lastLimit);
    while (elements.size() > lastLimit) {
        callback(elements.back());
        elements.pop_back();
    }
}

} // namespace opensmt

#endif //OPENSMT_SCOPEDVECTOR_H
