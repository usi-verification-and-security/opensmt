#ifndef OPENSMT_FUNUTILS_H
#define OPENSMT_FUNUTILS_H

#include <compare>
#include <concepts>
#include <functional>
#include <utility>

#define FORWARD(arg) std::forward<decltype(arg)>(arg)

namespace opensmt {
template<typename Op>
struct CompoundAssignOf;

template<>
struct CompoundAssignOf<std::plus<void>> {
    constexpr auto & operator()(auto & lhs, auto const & rhs) const {
        lhs += rhs;
        return lhs;
    }
};
template<>
struct CompoundAssignOf<std::minus<void>> {
    constexpr auto & operator()(auto & lhs, auto const & rhs) const {
        lhs -= rhs;
        return lhs;
    }
};
template<>
struct CompoundAssignOf<std::multiplies<void>> {
    constexpr auto & operator()(auto & lhs, auto const & rhs) const {
        lhs *= rhs;
        return lhs;
    }
};
template<>
struct CompoundAssignOf<std::divides<void>> {
    constexpr auto & operator()(auto & lhs, auto const & rhs) const {
        lhs *= rhs;
        return lhs;
    }
};

template<typename O = std::strong_ordering>
inline O intToOrdering(std::integral auto cmp) {
    if (cmp == 0) {
        return O::equivalent;
    } else if (cmp < 0) {
        return O::less;
    } else {
        return O::greater;
    }
}
} // namespace opensmt

#endif // OPENSMT_FUNUTILS_H
