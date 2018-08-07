/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT2 -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#include "BVSolver.h"

static SolverDescr descr_bv_solver("UF Solver", "Solver for Quantifier Free Bit Vectors");

BVSolver::BVSolver (SMTConfig & c, MainSolver& s, BVLogic& l, vec<DedElem> & d)
 : TSolver ((SolverId)descr_bv_solver, (const char*)descr_bv_solver, c, d)
 , mainSolver(s)
 , logic(l)
 , B(id, c, mainSolver, l, explanation, d, suggestions)
{ }

BVSolver::~BVSolver () { }

//
// The solver is informed of the existence of
// atom e. It might be useful for initializing
// the solver's data structures. This function is
// called before the actual solving starts.
//
lbool BVSolver::declareTerm(PTRef tr)
{
  assert(tr != PTRef_Undef);
  const lbool res = B.inform( tr );
  return res;
}

//
// Asserts a literal into the solver. If by chance
// you are able to discover inconsistency you may
// return false. The real consistency state will
// be checked with "check"
//
bool BVSolver::assertLit ( PtAsgn pta, bool reason )
{
    (void)reason;
    assert( pta.tr != PTRef_Undef );
    assert( pta.sgn != l_Undef );

    Pterm& t = logic.getPterm(pta.tr);
    if ( deduced[t.getVar()] != l_Undef && deduced[t.getVar()].polarity == pta.sgn && deduced[t.getVar()].deducedBy == id)
        return true;

    stack.push(pta);
    const bool res = B.assertLit(pta);

    assert( res || explanation.size() != 0 );

    return res;
}

//
// Saves a backtrack point
//
void BVSolver::pushBacktrackPoint ( )
{
    backtrack_points.push( stack.size( ) );
    //
    // Push a backtrack point inside the bitblaster
    //
    B.pushBacktrackPoint( );
}

//
// Restore a previous state.
// Also make sure you clean the deductions you
// did not communicate
//
void BVSolver::popBacktrackPoint ( )
{
    assert( backtrack_points.size( ) > 0 );
    size_t stack_new_size = backtrack_points.last();
    backtrack_points.pop();
    //
    // Restore stack size
    //
    while ( stack.size( ) > stack_new_size ) 
    {
        stack.pop();
    }
    //
    // Restore bitblaster state
    //
    B.popBacktrackPoint();
}

//
// Check for consistency. If flag is
// set make sure you run a complete check
//
TRes BVSolver::check( bool complete )
{
    if ( !complete ) return TR_SAT;
    assert( explanation.size() == 0 );

    // Here check for consistency.  No undefs allowed.
    const bool res = (B.check() == l_True ? true : false);

    assert(res || (explanation.size() != 0));
    return res ? TR_SAT : TR_UNSAT;
}

void BVSolver::computeModel( )
{
    B.computeModel( );
}

ValPair
BVSolver::getValue(PTRef tr)
{
    return B.getValue(tr);
}
