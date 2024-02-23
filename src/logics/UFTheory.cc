#include "Theory.h"
#include "TreeOps.h"
#include "DistinctRewriter.h"

PTRef UFTheory::preprocessBeforeSubstitutions(PTRef fla, PreprocessingContext const & context) {
    return context.perPartition ? fla : getLogic().mkAnd(fla, getLogic().learnEqTransitivity(fla));
}

PTRef UFTheory::preprocessAfterSubstitutions(PTRef fla, PreprocessingContext const & context) {
    fla = context.frameCount == 0 ? rewriteDistinctsKeepTopLevel(getLogic(), fla)
                               : rewriteDistincts(getLogic(), fla);
    AppearsInUfVisitor(getLogic()).visit(fla);
    return fla;
}

