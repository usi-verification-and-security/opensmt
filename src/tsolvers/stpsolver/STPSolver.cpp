//
// Created by Martin Blicha on 12.12.19.
//

#include "STPSolver.h"

static SolverDescr descr_stp_solver("STP Solver", "Solver for Simple Temporal Problem (Difference Logic)");

STPSolver::STPSolver(SMTConfig & c, LALogic & l)
        : TSolver((SolverId)descr_stp_solver, (const char*)descr_stp_solver, c)
        , logic(l)
        , mapper(l, store)          // store is initialized before mapper and graph, so these constructors are valid
        , graphMgr(store, mapper)  // similarly, mapper is initialized before graph (per declaration in header)
        , inv_bpoint(-1)
        , inv_asgn(PtAsgn_Undef)
{}

STPSolver::~STPSolver() = default;

// TODO: Ignore terms we don't care about instead of throwing an exception?
STPSolver::ParsedPTRef STPSolver::parseRef(PTRef ref) const {
    // inequalities are in the form (c <= (x + (-1 * y)))
    assert( logic.isNumLeq(ref) );
    Pterm &leq = logic.getPterm(ref);
    assert( logic.isNumConst(leq[0]) );  // TODO: Can the inequality be reversed?
    auto con = -logic.getNumConst(leq[0]);  // -'c': since we want the form (y <= x + c), the constant is negated
    assert( con.isInteger() );  // we're dealing with IDL for now
    auto c = static_cast<ptrdiff_t>(con.get_d());
    PTRef rhs = leq[1];  // 'x + (-1 * y)'

    PTRef x{}, y{};  // variables on the right hand side
    if (logic.isNumVar(rhs)) {  // inequality with a single positive variable
        x = rhs;
        y = PTRef_Undef;
    }
    else {  // right hand side contains at least a negative variable
        Pterm &rhsPt = logic.getPterm(rhs);
        PTRef mul{};  // (-1 * y) term
        if (logic.isNumPlus(rhs)) {  // usual DL inequality with two variables
            uint8_t ix = logic.isNumVar(rhsPt[0]) ? 0 : 1;
            uint8_t iy = 1 - ix;
            x = rhsPt[ix];
            mul = rhsPt[iy];
        }
        else { // RHS contains just a negative variable
            x = PTRef_Undef;
            mul = rhs;
        }

        assert( logic.isNumTimes(mul) );
        Pterm &mulPt = logic.getPterm(mul);
        assert( logic.isNumConst(mulPt[0]) && logic.getNumConst(mulPt[0]) == -1);
        y = mulPt[1];
        assert( logic.isNumVar(y) );
    }
    return ParsedPTRef{x, y, c};
}

EdgeRef STPSolver::createNegation(EdgeRef e) {
    const Edge &edge = store.getEdge(e);
    // TODO: The negation of edge cost as (-(cost+1)) only works for integer costs, not for real costs
    EdgeRef res = store.createEdge(edge.to, edge.from, -(edge.cost + 1));
    store.setNegation(e, res);
    return res;
}



void STPSolver::declareAtom(PTRef tr) {
    // This method is used from outside to tell the solver about a possible atom that can later be asserted positively
    // or negatively
    // Ignore everything else other than atoms of the form "x - y <= c"; i.e., variable minus variable is less or equal
    // to some constant
    // TODO: store information about the term tr if necessary

    if (isKnown(tr)) { return; }
    setKnown(tr);

    auto parsed = parseRef(tr);

    // find out if edge already exists (created as part of a negation)
    VertexRef x = mapper.getVertRef(parsed.x);
    VertexRef y = mapper.getVertRef(parsed.y);
    EdgeRef e = mapper.getEdgeRef(y, x, parsed.c);

    if (e != EdgeRef_Undef) {
        mapper.mapEdge(tr, e);  // edges created as negations of another atom can't yet exist in mapper
        return;
    }

    // create new variables in store
    if (x == VertRef_Undef) {
        x = store.createVertex();
        mapper.setVert(parsed.x, x);
    }
    if (y == VertRef_Undef) {
        y = store.createVertex();
        mapper.setVert(parsed.y, y);
    }
    // e is definitely EdgeRef_Undef
    e = store.createEdge(y, x, parsed.c);
    EdgeRef neg = createNegation(e);
    mapper.mapEdge(tr, e);
    mapper.registerEdge(neg);       // adding 'neg' to the 'edgesOf' map even without a PTRef to assign to it
}

bool STPSolver::assertLit(PtAsgn asgn) {
    // Actually asserting an atom to the solver - adding a new constraint to the current set
    // asgn.tr is the atom to add
    // asgn.sgn is the polarity (positive or negative)
    // TODO: process the addition of the constraint to the current set of constraints
    //      Return false if immediate conflict has been detected, otherwise return true
    //      Postpone actual checking of consistency of the extended set of constraints until call to the "check" method
    if (inv_asgn != PtAsgn_Undef) return false;            // no need to check anything if we're inconsistent already

    EdgeRef e = mapper.getEdgeRef(asgn.tr);
    assert( e != EdgeRef_Undef );
    EdgeRef neg = store.getEdge(e).neg;
    assert( neg != EdgeRef_Undef );

    EdgeRef set = (asgn.sgn == l_True) ? e : neg;   // edge corresponding to 'true' assignment of 'asgn.tr'
    EdgeRef nset = (set == e) ? neg : e;            //                       'false'

    // literal was already assigned or found as a consequence
    if (graphMgr.isTrue(set)) {
        return true;    // TODO: if a deduction is explicitly set, should we remember that?
    }
    // negation of literal was already assigned or found as a consequence
    if (graphMgr.isTrue(nset)) {
        inv_bpoint = backtrack_points.size();               // remember the first time we reached inconsistent state
        inv_asgn = asgn;
        has_explanation = true;                             // marks this TSolver as the cause of inconsistency
        return false;
    }

    // The assignment isn't decided yet, so we set it as true and find all of its consequences
    graphMgr.setTrue(set, asgn);
    vec<EdgeRef> deductions = graphMgr.findConsequences(set);

    // pass all found deductions to TSolver
    PTRef nleq = mapper.getPTRef(nset);
    if (nleq != PTRef_Undef)
        storeDeduction(PtAsgn_reason(nleq, l_False, PTRef_Undef));

    for (auto eRef : deductions) {
        PTRef leq = mapper.getPTRef(eRef);
        nleq = mapper.getPTRef(store.getNegation(eRef));
        if (leq != PTRef_Undef && !hasPolarity(leq))
            storeDeduction(PtAsgn_reason(leq, l_True, PTRef_Undef));
        if (nleq != PTRef_Undef && !hasPolarity(nleq))
            storeDeduction(PtAsgn_reason(nleq, l_False, PTRef_Undef));
    }
    return true;
}

TRes STPSolver::check(bool b) {
    // The main method checking the consistency of the current set of constraints
    // Return SAT if the current set of constraints is satisfiable, UNSAT if unsatisfiable
    // TODO: implement the main check of consistency

    // we check the validity of each assertLit, so this just returns the consistency of current state
    return inv_asgn == PtAsgn_Undef ? TRes::SAT : TRes::UNSAT;
}

void STPSolver::clearSolver() {
    TSolver::clearSolver();
    graphMgr.clear();
    mapper.clear();
    store.clear();
}

void STPSolver::print(ostream & out) {

}

void STPSolver::pushBacktrackPoint() {
    // Marks a checkpoint for the set of constraints in the solver
    // Important for backtracking
    TSolver::pushBacktrackPoint();
    backtrack_points.push(graphMgr.getAddedCount());
}

void STPSolver::popBacktrackPoint() {
    // This is just for compatibility with older architecture
    // Typically multiple backtrack points are popped together, hence popBacktackPoints is the important method to implement
    popBacktrackPoints(1);
}

void STPSolver::popBacktrackPoints(unsigned int i) {
    // This method is called after unsatisfiable state is detected
    // The solver should remove all constraints that were pushed to the solver in the last "i" backtrackpoints
    if (!i) return;
    assert( backtrack_points.size() >= i );
    if (inv_bpoint > backtrack_points.size() - i) {  // if we returned back to a consistent state, we reset inv_bpoint
        inv_bpoint = 0;
        inv_asgn = PtAsgn_Undef;
        has_explanation = false;
    }

    backtrack_points.shrink(i -1); // pop 'i-1' values from the backtrack stack
    graphMgr.removeAfter(backtrack_points.last());
    backtrack_points.shrink(1);
    // no need to modify mapper or store - the values stored there can't change
    for (size_t j = 0; j < i; ++j)
        TSolver::popBacktrackPoint();
}

ValPair STPSolver::getValue(PTRef pt) {
    // In the current model, get the value (represented as string) of the term "pt".
    VertexRef v = mapper.getVertRef(pt);
    if (v == VertRef_Undef || model == nullptr || !model->hasValue(v))
        return ValPair_Undef;

    ptrdiff_t value = model->getValue(v);
    return ValPair(pt, std::to_string(value).c_str());
}

void STPSolver::computeModel() {
    // In case of satisfiability prepare a model witnessing the satisfiability of the current set of constraints
    model = std::unique_ptr<STPModel>(new STPModel(store, graphMgr.getGraph()));
    model->createModel();
}

void STPSolver::getConflict(bool b, vec<PtAsgn> & vec) {
    // In case of unsatisfiability, return the witnessing subset of constraints
    // The bool parameter can be ignored, the second parameter is the output parameter
    if (inv_asgn == PtAsgn_Undef) return;  // TODO: how to handle call in consistent state?
    vec.push(inv_asgn);
    EdgeRef e = mapper.getEdgeRef(inv_asgn.tr);
    if (inv_asgn.sgn == l_True) {
        e = store.getNegation(e);
    }
    assert(graphMgr.isTrue(e) );
    graphMgr.findExplanation(e, vec);
}

Logic & STPSolver::getLogic() {
    return logic;
}

bool STPSolver::isValid(PTRef tr) {
    return logic.isNumLeq(tr);
}
