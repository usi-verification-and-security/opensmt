//
// Created by Martin Blicha on 12.12.19.
//

#include "STPSolver.h"

static SolverDescr descr_stp_solver("STP Solver", "Solver for Simple Temporal Problem (Difference Logic)");

STPSolver::STPSolver(SMTConfig & c, LALogic & l, vec<DedElem> & d)
        : TSolver((SolverId)descr_stp_solver, (const char*)descr_stp_solver, c, d)
        , logic(l)
{
    has_explanation = true;
}

STPSolver::~STPSolver() = default;

ParsedRef STPSolver::parseRef(PTRef ref) {
    // inequalities are in the form (c <= (x + (-1 * y)))
    assert( logic.isNumLeq(ref) );
    Pterm &leq = logic.getPterm(ref);
    assert( logic.isNumConst(leq[0]) );
    auto con = -logic.getNumConst(leq[0]);  // -'c': since we want the form (y <= x + c), the constant is negated
    PTRef diff = leq[1];                        // 'x + (-1 * y)'

    assert( logic.isNumPlus(diff) );
    Pterm &diffPt = logic.getPterm(diff);
    uint8_t ix = logic.isNumVar(diffPt[0]) ? 0 : 1;     // index of 'x'
    uint8_t iy = 1 - ix;                                    // index of '-1 * y'
    PTRef x = diffPt[ix];                       // 'x'
    assert( logic.isNumTimes(diffPt[iy]) );

    Pterm &mult = logic.getPterm(diffPt[iy]);   // '-1 * y'
    assert( logic.isNumConst(mult[0]) && logic.getNumConst(mult[0]) == -1 );
    assert( logic.isNumVar(mult[1]) );
    PTRef y = mult[1];                          // 'y'

    return ParsedRef{x, y, diff, con};
}

void STPSolver::declareAtom(PTRef tr) {
    // This method is used from outside to tell the solver about a possible atom that can later be asserted positively
    // or negatively
    // Ignore everything else other than atoms of the form "x - y <= c"; i.e., variable minus variable is less or equal
    // to some constant
    // TODO: store information about the term tr if necessary
    auto parsed = parseRef(tr);
    auto x = store.createVertex();
    auto y = store.createVertex();
    auto e = store.createEdge(y, x, parsed.c);
    mapper.setVert(parsed.x, x);
    mapper.setVert(parsed.y, y);
    // TODO: is the difference ref unique for each created (x + (-1*y)) ?
    mapper.setEdge(parsed.diff, e);
}

bool STPSolver::assertLit(PtAsgn asgn, bool b) {
    // Actually asserting an atom to the solver - adding a new constraint to the current set
    // asgn.tr is the atom to add
    // asgn.sgn is the polarity (positive or negative)
    // TODO: process the addition of the constraint to the current set of constraints
    //      Return false if immediate conflict has been detected, otherwise return true
    //      Postpone actual checking of consistency of the extended set of constraints until call to the "check" method

    return true;
}

TRes STPSolver::check(bool b) {
    // The main method checking the consistency of the current set of constraints
    // Return SAT if the current set of constraints is satisfiable, UNSAT if unsatisfiable
    // TODO: implement the main check of consistency

    return TRes::SAT;
}

void STPSolver::clearSolver() {
    TSolver::clearSolver();
}

void STPSolver::print(ostream & out) {

}

void STPSolver::pushBacktrackPoint() {
    // Marks a checkpoint for the set of constraints in the solver
    // Important for backtracking
    TSolver::pushBacktrackPoint();
}

void STPSolver::popBacktrackPoint() {
    // This is just for compatibility with older architecture
    // Typically multiple backtrack points are popped together, hence popBacktackPoints is the important method to implement
    popBacktrackPoints(1);
}

void STPSolver::popBacktrackPoints(unsigned int i) {
    // This method is called after unsatisfiable state is detected
    // The solver should remove all constraints that were pushed to the solver in the last "i" backtrackpoints
    TSolver::popBacktrackPoints(i);
}

ValPair STPSolver::getValue(PTRef pt) {
    // In the current model, get the value (represented as string) of the term "pt".
    return ValPair();
}

void STPSolver::computeModel() {
    // In case of satisfiability prepare a model witnessing the satisfiability of the current set of constraints

}

void STPSolver::getConflict(bool b, vec<PtAsgn> & vec) {
    // In case of unsatisfiability, return the witnessing subset of constraints
    // The bool parameter can be ignored, the second parameter is the output parameter

}

PtAsgn_reason STPSolver::getDeduction() {
    return PtAsgn_reason();
}


Logic & STPSolver::getLogic() {
    return logic;
}

bool STPSolver::isValid(PTRef tr) {
    return false;
}
