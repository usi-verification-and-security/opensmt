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

    [[nodiscard]] std::size_t size() const { return elements.size(); }

    [[nodiscard]] T * data() { return elements.data(); }
    [[nodiscard]] T const * data() const { return elements.data(); }

    [[nodiscard]] auto begin() const { return elements.begin(); }
    [[nodiscard]] auto end() const { return elements.end(); }

    [[nodiscard]] auto begin() { return elements.begin(); }
    [[nodiscard]] auto end() { return elements.end(); }
};

template<typename T>
void ScopedVector<T>::popScope() {
    popScope([](T const &) {});
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

#endif // OPENSMT_SCOPEDVECTOR_H
