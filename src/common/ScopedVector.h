/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_SCOPEDVECTOR_H
#define OPENSMT_SCOPEDVECTOR_H

#include <cassert>
#include <stdexcept>
#include <string>
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

    [[nodiscard]] std::size_t topScopeEmpty() const { return topScopeSize() == 0; }
    [[nodiscard]] std::size_t topScopeSize() const { return size() - sizeBeforeTopScope(); }

    [[nodiscard]] auto topScopeBegin() const { return begin() + sizeBeforeTopScope(); }
    [[nodiscard]] auto topScopeEnd() const { return end(); }

    [[nodiscard]] auto topScopeBegin() { return begin() + sizeBeforeTopScope(); }
    [[nodiscard]] auto topScopeEnd() { return end(); }

    [[nodiscard]] T const * topScopeData() const { return data() + sizeBeforeTopScope(); }
    [[nodiscard]] T * topScopeData() { return data() + sizeBeforeTopScope(); }

    [[nodiscard]] std::size_t scopeEmpty(std::size_t idx) const { return scopeSize(idx) == 0; }
    [[nodiscard]] std::size_t scopeSize(std::size_t idx) const;

    [[nodiscard]] auto scopeBegin(std::size_t idx) const { return begin() + sizeBeforeScope(idx); }
    [[nodiscard]] auto scopeEnd(std::size_t idx) const;

    [[nodiscard]] auto scopeBegin(std::size_t idx) { return begin() + sizeBeforeScope(idx); }
    [[nodiscard]] auto scopeEnd(std::size_t idx);

    [[nodiscard]] T const * scopeData(std::size_t idx) const { return data() + sizeBeforeScope(idx); }
    [[nodiscard]] T * scopeData(std::size_t idx) { return data() + sizeBeforeScope(idx); }

    // Views to just the top scope
    inline auto topScope() const;
    inline auto topScope();

    // Views to just a scope
    inline auto scope(std::size_t idx) const;
    inline auto scope(std::size_t idx);

protected:
    template<typename>
    class TopScopeView;
    template<typename>
    class ScopeView;

    inline bool isValidScopeIdx(std::size_t idx) const;
    inline void checkScopeIdx(std::size_t idx) const;

    inline std::size_t sizeBeforeTopScope() const;
    inline std::size_t sizeBeforeScope(std::size_t idx) const;
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

template<typename T>
bool ScopedVector<T>::isValidScopeIdx(std::size_t idx) const {
    return idx < scopeCount();
}

template<typename T>
void ScopedVector<T>::checkScopeIdx(std::size_t idx) const {
    if (isValidScopeIdx(idx)) { return; }
    throw std::out_of_range{"Scope index out of range: " + std::to_string(idx)};
}

template<typename T>
std::size_t ScopedVector<T>::sizeBeforeTopScope() const {
    if (limits.empty()) { return 0; }
    return limits.back();
}

template<typename T>
std::size_t ScopedVector<T>::sizeBeforeScope(std::size_t idx) const {
    checkScopeIdx(idx);
    if (idx == 0) { return 0; }
    return limits[idx - 1];
}

template<typename T>
std::size_t ScopedVector<T>::scopeSize(std::size_t idx) const {
    if (idx == scopeCount() - 1) { return topScopeSize(); }
    return sizeBeforeScope(idx + 1) - sizeBeforeScope(idx);
}

template<typename T>
auto ScopedVector<T>::scopeEnd(std::size_t idx) const {
    if (idx == scopeCount() - 1) { return topScopeEnd(); }
    return begin() + sizeBeforeScope(idx + 1);
}

template<typename T>
auto ScopedVector<T>::scopeEnd(std::size_t idx) {
    if (idx == scopeCount() - 1) { return topScopeEnd(); }
    return begin() + sizeBeforeScope(idx + 1);
}

template<typename T>
template<typename VectorT>
class ScopedVector<T>::TopScopeView {
public:
    explicit TopScopeView(VectorT & scopedVector_) : scopedVector{scopedVector_} {}

    bool empty() const noexcept { return scopedVector.topScopeEmpty(); }
    std::size_t size() const noexcept { return scopedVector.topScopeSize(); }

    auto begin() const noexcept { return scopedVector.topScopeBegin(); }
    auto end() const noexcept { return scopedVector.topScopeEnd(); }

    auto begin() noexcept { return scopedVector.topScopeBegin(); }
    auto end() noexcept { return scopedVector.topScopeEnd(); }

    T const * data() const noexcept { return scopedVector.topScopeData(); }
    T * data() noexcept { return scopedVector.topScopeData(); }

protected:
    VectorT & scopedVector;
};

template<typename T>
template<typename VectorT>
class ScopedVector<T>::ScopeView {
public:
    explicit ScopeView(VectorT & scopedVector_, std::size_t idx_) : scopedVector{scopedVector_}, idx{idx_} {}

    bool empty() const noexcept { return scopedVector.scopeEmpty(idx); }
    std::size_t size() const noexcept { return scopedVector.scopeSize(idx); }

    auto begin() const noexcept { return scopedVector.scopeBegin(idx); }
    auto end() const noexcept { return scopedVector.scopeEnd(idx); }

    auto begin() noexcept { return scopedVector.scopeBegin(idx); }
    auto end() noexcept { return scopedVector.scopeEnd(idx); }

    T const * data() const noexcept { return scopedVector.scopeData(idx); }
    T * data() noexcept { return scopedVector.scopeData(idx); }

protected:
    VectorT & scopedVector;
    std::size_t idx;
};

template<typename T>
auto ScopedVector<T>::topScope() const {
    return TopScopeView<ScopedVector const>{*this};
}

template<typename T>
auto ScopedVector<T>::topScope() {
    return TopScopeView<ScopedVector>{*this};
}

template<typename T>
auto ScopedVector<T>::scope(std::size_t idx) const {
    return ScopeView<ScopedVector const>{*this, idx};
}

template<typename T>
auto ScopedVector<T>::scope(std::size_t idx) {
    return ScopeView<ScopedVector>{*this, idx};
}
} // namespace opensmt

#endif // OPENSMT_SCOPEDVECTOR_H
