#include "Theory.h"
#include "ArithmeticEqualityRewriter.h"

//
// Unit propagate with simplifications and split equalities into
// inequalities.  If partitions cannot mix, only do the splitting to
// inequalities.
//
bool LRATheory::simplify(const vec<PFRef>& formulas, PartitionManager& pmanager, int curr)
{
    auto & currentFrame = pfstore[formulas[curr]];
    if (this->keepPartitions()) {
        vec<PTRef> & flas = currentFrame.formulas;
        for (int i = 0; i < flas.size(); ++i) {
            PTRef & fla = flas[i];
            PTRef old = flas[i];
            auto arr = ArithmeticEqualityRewriter(lralogic);
            fla = arr.rewrite(old);
            notOkToPartition = arr.getAndClearNotOkToPartition();
            pmanager.transferPartitionMembership(old, fla);
        }
        currentFrame.root = getLogic().mkAnd(flas);
    } else {
        PTRef coll_f = getCollateFunction(formulas, curr);
        auto subs_res = computeSubstitutions(coll_f);
        PTRef finalFla = flaFromSubstitutionResult(subs_res);
        getTSolverHandler().setSubstitutions(subs_res.usedSubstitution);
        auto arr = ArithmeticEqualityRewriter(lralogic);
        currentFrame.root = arr.rewrite(finalFla);
        notOkToPartition = arr.getAndClearNotOkToPartition();
    }
    return true;
}