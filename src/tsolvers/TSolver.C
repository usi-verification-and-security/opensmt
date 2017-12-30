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

void TSolver::popBacktrackPoint()
{
    assert( deductions_last.size() > 0 );
    assert( deductions_lim.size() > 0 );
    deductions_next = deductions_last.last();
    deductions_last.pop();
    // Restore deductions
    size_t new_deductions_size = deductions_lim.last( );
    deductions_lim.pop();
    while (th_deductions.size_() > new_deductions_size) {
        PtAsgn_reason asgn = th_deductions.last();
        assert(deduced[getLogic().getPterm(asgn.tr).getVar()] != l_Undef);
        deduced[getLogic().getPterm(asgn.tr).getVar()] = DedElem_Undef;
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
    uint32_t id = Idx(getLogic().getPterm(tr).getId());
    if (known_preds.size() <= id)
        return false;
    return known_preds[id];
}

// MB: setPolarity and clearPolarity moved to .C file to remove the macros from the header

void  TSolver::setPolarity(PTRef tr, lbool p)
{
    if (polarityMap.has(tr)) { polarityMap[tr] = p; }
    else { polarityMap.insert(tr, p); }
#ifdef VERBOSE_EUF
    cerr << "Setting polarity " << getLogic().printTerm(tr) << " " << tr.x << endl;
#endif
}

void  TSolver::clearPolarity(PTRef tr)
{
    polarityMap[tr] = l_Undef;
#ifdef VERBOSE_EUF
    cerr << "Clearing polarity " << getLogic().printTerm(tr) << " " << tr.x << endl;
#endif
}
