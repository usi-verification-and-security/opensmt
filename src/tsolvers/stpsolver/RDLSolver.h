#ifndef OPENSMT_RDLSOLVER_H
#define OPENSMT_RDLSOLVER_H

#include "STPSolver.h"
#include "Delta.h"
#include "Converter.h"
#include "ModelBuilder.h"

class RDLSolver : public STPSolver<Delta> {
public:
    RDLSolver(SMTConfig &c, ArithLogic &l) : STPSolver(c, l) {};
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

template<>
void STPSolver<Delta>::fillTheoryFunctions(ModelBuilder & modelBuilder) const {
    auto knownValues = this->model->getAllValues();
    // Now we need to compute the proper values as Rationals, not as \delta-Rationals
    // Compute the right value for delta:
    Delta delta;
    FastRational deltaVal;
    bool deltaSet = false;
    // I need to iterate over all edges and find the minimum from deltas making the edges true
    auto const & edges = this->model->getGraph().addedEdges;
    for (EdgeRef edgeRef : edges) {
        auto const &edge = store.getEdge(edgeRef);
        Delta realDiff = knownValues.at(edge.from) - knownValues.at(edge.to);
        Delta const &upperBound = edge.cost;
        assert(upperBound.R() >= realDiff.R());
        if (realDiff.R() < upperBound.R() and realDiff.D() > upperBound.D()) {
            Real valOfDelta = (upperBound.R() - realDiff.R()) / (realDiff.D() - upperBound.D());
            assert(valOfDelta > 0);
            if (not deltaSet or delta > valOfDelta) {
                deltaSet = true;
                delta = valOfDelta;
            }
        }
    }
    if (not deltaSet || delta > 1) {
        deltaVal = opensmt::Number(1);
    } else {
        deltaVal = delta.R()/2;
    }

    for (auto const & entry : knownValues) {
        PTRef var = this->mapper.getPTRef(entry.first);
        if (var == PTRef_Undef) { continue; }
        assert(logic.isVar(var));
        Delta const & varDeltaValue = entry.second;
        FastRational varValue = varDeltaValue.R() + varDeltaValue.D() * deltaVal;
        PTRef val = logic.mkRealConst(varValue);
        modelBuilder.addVarValue(var, val);
    }
}

#endif //OPENSMT_RDLSOLVER_H
