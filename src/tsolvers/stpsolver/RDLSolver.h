#ifndef OPENSMT_RDLSOLVER_H
#define OPENSMT_RDLSOLVER_H

#include "STPSolver.h"
#include "Delta.h"
#include "Converter.h"

class RDLSolver : public STPSolver<Delta> {
public:
    RDLSolver(SMTConfig &c, LALogic &l) : STPSolver(c, l) {};
};

template<>
Delta Converter<Delta>::getValue(const FastRational &val) {
    return Delta(val, 0);
}

template<>
Delta Converter<Delta>::getValue(ptrdiff_t val) {
    return Delta(FastRational(val, 1), 0);
}

template<>
Delta Converter<Delta>::negate(const Delta &val) {
    assert(!val.hasDelta());
    // not(a-b <= c) == (b-a < -c) == (b-a <= -c-delta)
    return Delta(-val.R(), -1);
}

template<>
std::string Converter<Delta>::show(const Delta &val) {
    return val.printValue();
}

#endif //OPENSMT_RDLSOLVER_H
