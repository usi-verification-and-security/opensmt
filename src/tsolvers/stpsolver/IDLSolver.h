#ifndef OPENSMT_IDLSOLVER_H
#define OPENSMT_IDLSOLVER_H

#include "Converter.h"
#include "STPSolver.h"
#include "SafeInt.h"

#include <models/ModelBuilder.h>

namespace opensmt {
class IDLSolver : public STPSolver<SafeInt> {
public:
    IDLSolver(SMTConfig & c, ArithLogic & l) : STPSolver(c, l) {};
};

template<>
SafeInt Converter<SafeInt>::getValue(Number const & val) {
    assert(castInteger(val).tryGetValue());
    return SafeInt(static_cast<ptrdiff_t>(*castInteger(val).tryGetValue()));
}

template<>
SafeInt Converter<SafeInt>::getValue(ptrdiff_t val) {
    return SafeInt(val);
}

template<>
SafeInt Converter<SafeInt>::negate(SafeInt const & val) {
    return SafeInt(-(val.value() + 1));
}

template<>
std::string Converter<SafeInt>::show(SafeInt const & val) {
    return std::to_string(val.value());
}

template<>
void STPSolver<SafeInt>::fillTheoryFunctions(ModelBuilder & modelBuilder) const {
    auto knownValues = this->model->getAllValues();
    for (auto const & entry : knownValues) {
        PTRef var = this->mapper.getPTRef(entry.first);
        if (var == PTRef_Undef) { continue; }
        assert(logic.isVar(var));
        auto stringVal = Converter<SafeInt>::show(entry.second);
        PTRef val = logic.mkConst(stringVal.c_str());
        modelBuilder.addVarValue(var, val);
    }
}
} // namespace opensmt

#endif // OPENSMT_IDLSOLVER_H
