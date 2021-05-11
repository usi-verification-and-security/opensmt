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
        for (PTRef & fla : flas) {
            PTRef old = fla;
            fla = rewriter.rewrite(old).first;
            pmanager.transferPartitionMembership(old, fla);
        }
        currentFrame.root = getLogic().mkAnd(flas);
    } else {
        PTRef coll_f = getCollateFunction(formulas, curr);
        auto subs_res = computeSubstitutions(coll_f);
        PTRef finalFla = flaFromSubstitutionResult(subs_res);
        setSubstitutions(std::move(subs_res.usedSubstitution));
        currentFrame.root = rewriter.rewrite(finalFla).first;
    }
    notOkToPartition = rewriter.getAndClearNotOkToPartition();
    AppearsInUfVisitor(getLogic()).visit(currentFrame.root);
    return true;
}
