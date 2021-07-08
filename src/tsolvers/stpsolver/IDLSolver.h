#ifndef OPENSMT_IDLSOLVER_H
#define OPENSMT_IDLSOLVER_H

#include "STPSolver.h"
#include "SafeInt.h"
#include "Converter.h"

class IDLSolver : public STPSolver<SafeInt> {
public:
    IDLSolver(SMTConfig &c, LALogic &l) : STPSolver(c, l) {};
};

template<>
SafeInt Converter<SafeInt>::getValue(const FastRational &val) {
    assert(val.isInteger());
    return SafeInt(static_cast<ptrdiff_t>(val.get_d()));
}

template<>
SafeInt Converter<SafeInt>::getValue(ptrdiff_t val) {
    return SafeInt(val);
}

template<>
SafeInt Converter<SafeInt>::negate(const SafeInt &val) {
    return SafeInt(-(val.value() + 1));
}

template<>
std::string Converter<SafeInt>::show(const SafeInt &val) {
    return std::to_string(val.value());
}

#endif //OPENSMT_IDLSOLVER_H
