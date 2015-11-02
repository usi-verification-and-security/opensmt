#include "TSolver.h"

void TSolver::popBacktrackPoint()
{
    assert( deductions_last.size( ) > 0 );
    assert( deductions_lim.size( ) > 0 );
    deductions_next = deductions_last.last();
    deductions_last.pop();
    // Restore deductions
    size_t new_deductions_size = deductions_lim.last( );
    deductions_lim.pop( );
    while (th_deductions.size_() > new_deductions_size) {
        PtAsgn_reason asgn = th_deductions.last();
        assert(deduced[getLogic().getPterm(asgn.tr).getVar()] != l_Undef);
#ifdef VERBOSE_EUF
        cerr << "Clearing deduction " << getLogic().printTerm(asgn.tr) << endl;
#endif
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
