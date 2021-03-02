#include "UFLRATheory.h"
#include "ArithmeticEqualityRewriter.h"

bool UFLRATheory::simplify(const vec<PFRef>& formulas, PartitionManager &pmanager, int curr)
{
    auto & currentFrame = pfstore[formulas[curr]];
    // Take care of UF simplifications as well
    if (this->keepPartitions()) {
        currentFrame.root = getLogic().mkAnd(currentFrame.formulas);
        auto arr = ArithmeticEqualityRewriter(lralogic);
        currentFrame.root = arr.rewrite(currentFrame.root);
        notOkToPartition = arr.getAndClearNotOkToPartition();
    } else {
        PTRef coll_f = getCollateFunction(formulas, curr);
        auto subs_res = computeSubstitutions(coll_f);
        PTRef finalFla = flaFromSubstitutionResult(subs_res);
        getTSolverHandler().setSubstitutions(subs_res.usedSubstitution);
        currentFrame.root = ArithmeticEqualityRewriter(lralogic).rewrite(finalFla);
    }
    return true;
}
