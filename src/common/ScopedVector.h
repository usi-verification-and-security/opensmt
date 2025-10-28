/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_SCOPEDVECTOR_H
#define OPENSMT_SCOPEDVECTOR_H

#include <cassert>
#include <vector>

namespace opensmt {
template<typename T>
class ScopedVector {
    std::vector<T> elements;
    std::vector<unsigned> limits;

public:
    using value_type = T;
    using reference = T &;
    using const_reference = T const &;
    using pointer = T *;
    using const_pointer = T const *;

    using size_type = std::size_t;

    using iterator = typename decltype(elements)::iterator;
    using const_iterator = typename decltype(elements)::const_iterator;

    void push(T const & element) { return elements.push_back(element); }

    void pushScope() { limits.push_back(elements.size()); }
    inline void popScope();
    template<typename TFun>
    inline void popScope(TFun callback);

    inline void clear();

    [[nodiscard]] bool empty() const { return elements.empty(); }
    [[nodiscard]] std::size_t size() const { return elements.size(); }

    [[nodiscard]] auto begin() const { return elements.begin(); }
    [[nodiscard]] auto end() const { return elements.end(); }

    [[nodiscard]] auto begin() { return elements.begin(); }
    [[nodiscard]] auto end() { return elements.end(); }

    [[nodiscard]] T const * data() const { return elements.data(); }
    [[nodiscard]] T * data() { return elements.data(); }

    [[nodiscard]] std::size_t scopeCount() const { return limits.size() + 1; }
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

template<typename T>
void ScopedVector<T>::clear() {
    elements.clear();
    limits.clear();
}
} // namespace opensmt

#endif // OPENSMT_SCOPEDVECTOR_H
