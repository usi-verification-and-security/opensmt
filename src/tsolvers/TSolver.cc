#include "TSolver.h"
#include "Logic.h"

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

bool TSolver::isKnown(PTRef tr)
{
    uint32_t tid = Idx(getLogic().getPterm(tr).getId());
    return tid < known_preds.size_() && known_preds[tid];
}

void TSolver::setKnown(PTRef tr) {
    auto tid = Idx(getLogic().getPterm(tr).getId());
    while (known_preds.size_() <= tid) {
        known_preds.push(false);
    }
    known_preds[tid] = true;
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