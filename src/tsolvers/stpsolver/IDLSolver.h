#ifndef OPENSMT_IDLSOLVER_H
#define OPENSMT_IDLSOLVER_H

#include "STPSolver.cpp"
#include "SafeInt.hpp"

template<> SafeInt STPSolver<SafeInt>::convert(const opensmt::Number &cost) {
    assert(cost.isInteger());
    return {static_cast<ptrdiff_t>(cost.get_d())};
}

template<> SafeInt STPSolver<SafeInt>::negate(const SafeInt &cost) {
    return -(cost + 1);
}

template<> std::string STPSolver<SafeInt>::show(const SafeInt &val) {
    return std::to_string(val.value());
}

#endif //OPENSMT_IDLSOLVER_H
