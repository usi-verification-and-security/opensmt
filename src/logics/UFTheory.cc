#include "Theory.h"
#include "TreeOps.h"
#include "DistinctRewriter.h"

PTRef UFTheory::simplifyTogether(vec<PTRef> const & assertions, bool isBaseFrame) {
    PTRef frameFormula = getLogic().mkAnd(assertions);
    PTRef trans = getLogic().learnEqTransitivity(frameFormula);
    frameFormula = getLogic().mkAnd(frameFormula, trans);
    frameFormula = applySubstitutionBasedSimplificationIfEnabled(frameFormula);
    frameFormula = isBaseFrame ? rewriteDistinctsKeepTopLevel(getLogic(), frameFormula)
                                  : rewriteDistincts(getLogic(), frameFormula);
    AppearsInUfVisitor(getLogic()).visit(frameFormula);
    return frameFormula;
}

vec<PTRef> UFTheory::simplifyIndividually(vec<PTRef> const& formulas, PartitionManager &, bool isBaseFrame)
{
    vec<PTRef> rewrittenFormulas;
    formulas.copyTo(rewrittenFormulas);
    AppearsInUfVisitor visitor(getLogic());

    for (PTRef & fla : rewrittenFormulas) {
        fla = isBaseFrame ? rewriteDistinctsKeepTopLevel(getLogic(), fla) : rewriteDistincts(getLogic(), fla);
        visitor.visit(fla);
    }
    return rewrittenFormulas;
}

