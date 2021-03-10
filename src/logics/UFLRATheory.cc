#include "UFLRATheory.h"
#include "TreeOps.h"
#include "ArithmeticEqualityRewriter.h"

bool UFLRATheory::simplify(const vec<PFRef>& formulas, PartitionManager &pmanager, int curr)
{
    auto & currentFrame = pfstore[formulas[curr]];
    // Take care of UF simplifications as well
    ArithmeticEqualityRewriter rewriter(lralogic);
    if (this->keepPartitions()) {
        vec<PTRef> & flas = currentFrame.formulas;
        ArithmeticEqualityRewriter rewriter(lralogic);
        for (PTRef & fla : flas) {
            PTRef old = fla;
            fla = rewriter.rewrite(old);
            pmanager.transferPartitionMembership(old, fla);
        }
        notOkToPartition = rewriter.getAndClearNotOkToPartition();
        currentFrame.root = getLogic().mkAnd(flas);
    } else {
        PTRef coll_f = getCollateFunction(formulas, curr);
        auto subs_res = computeSubstitutions(coll_f);
        PTRef finalFla = flaFromSubstitutionResult(subs_res);
        getTSolverHandler().setSubstitutions(subs_res.usedSubstitution);
        currentFrame.root = ArithmeticEqualityRewriter(lralogic).rewrite(finalFla);
    }
    AppearsInUfVisitor(getLogic()).visit(currentFrame.root);
    return true;
}
