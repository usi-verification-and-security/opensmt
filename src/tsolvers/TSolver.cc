#include "TSolver.h"
#include "Logic.h"
#include "OsmtInternalException.h"

void TSolver::clearSolver()
{
    explanation.clear();
    th_deductions.clear();
    deductions_next = 0;
    deductions_lim.clear();
    deductions_last.clear();
    suggestions.clear();
    informed_PTRefs.clear();
    has_explanation = false;
    backtrack_points.clear();
}

void TSolver::popBacktrackPoints(unsigned int counter) {
    for (unsigned int i = 0; i < counter; ++i) {
        this->popBacktrackPoint();
    }
}

void TSolver::popBacktrackPoint()
{
    assert( deductions_last.size() > 0 );
    assert( deductions_lim.size() > 0 );
    deductions_next = deductions_last.last();
    deductions_last.pop();
    // Restore deductions
    size_t new_deductions_size = deductions_lim.last();
    deductions_lim.pop();
    while (th_deductions.size_() > new_deductions_size) {
        PtAsgn_reason asgn = th_deductions.last();
        clearPolarity(asgn.tr);
        th_deductions.pop();
    }
    assert( deductions_next <= th_deductions.size_() );
    assert( deductions_last.size( ) == deductions_lim.size( ) );
}

void TSolver::pushBacktrackPoint()
{
    deductions_lim.push(th_deductions.size());
    deductions_last.push(deductions_next);
    assert(deductions_last.size() == deductions_lim.size());
}

// MB: setPolarity and clearPolarity moved to .C file to remove the macros from the header

void  TSolver::setPolarity(PTRef tr, lbool p)
{
    if (polarityMap.has(tr)) { polarityMap[tr] = p; }
    else { polarityMap.insert(tr, p); }
}

void TSolver::getNewSplits(vec<PTRef>&)
{
    // Default implementation does not give splits
}

bool TSolver::hasNewSplits() {
    return splitondemand.size() > 0;
}

PtAsgn_reason TSolver::getDeduction() {
    if (deductions_next >= th_deductions.size_()) {
        return PtAsgn_reason_Undef;
    }
    return th_deductions[deductions_next++];
}

vec<PtAsgn> TSolver::getReasonFor(PtAsgn lit) {
    pushBacktrackPoint();
    // assert with negated polarity
    assert(lit.sgn != l_Undef);
    bool sat = assertLit(PtAsgn(lit.tr, lit.sgn == l_True ? l_False : l_True));
    if (sat) {
        assert(false);
        throw OsmtInternalException("Error in computing reason for theory-propagated literal");
    }
    vec<PtAsgn> conflict;
    getConflict(conflict);
    popBacktrackPoint();
#ifdef STATISTICS
    if (conflict.size() > generalTSolverStats.max_reas_size)
        generalTSolverStats.max_reas_size = conflict.size();
    if (conflict.size() < generalTSolverStats.min_reas_size)
        generalTSolverStats.min_reas_size = conflict.size();
    generalTSolverStats.reasons_sent ++;
    generalTSolverStats.avg_reas_size += conflict.size();
#endif // STATISTICS
    return conflict;
}

void TSolver::printStatistics(std::ostream & os) {
    os << "; -------------------------\n";
    os << "; STATISTICS FOR " << getName() << '\n';
    os << "; -------------------------\n";
    generalTSolverStats.printStatistics(os);
}