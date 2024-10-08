#include "Theory.h"

#include <common/TreeOps.h>
#include <rewriters/Rewritings.h>

namespace opensmt {

PTRef UFTheory::preprocessBeforeSubstitutions(PTRef fla, PreprocessingContext const & context) {
    return context.perPartition ? fla : getLogic().mkAnd(fla, getLogic().learnEqTransitivity(fla));
}

PTRef UFTheory::preprocessAfterSubstitutions(PTRef fla, PreprocessingContext const & context) {
    using namespace opensmt;
    fla = context.frameCount == 0 ? rewriteDistinctsKeepTopLevel(getLogic(), fla)
                               : rewriteDistincts(getLogic(), fla);
    AppearsInUfVisitor(getLogic()).visit(fla);
    return fla;
}

}
