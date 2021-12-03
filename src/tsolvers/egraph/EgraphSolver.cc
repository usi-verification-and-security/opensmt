/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso

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

/********************************************************************
The algorithm and data structures are inspired by the following paper:

@article{Detlefs:2005:STP:1066100.1066102,
 author = {Detlefs, David and Nelson, Greg and Saxe, James B.},
 title = {Simplify: A Theorem Prover for Program Checking},
 journal = {J. ACM},
 issue_date = {May 2005},
 volume = {52},
 number = {3},
 month = may,
 year = {2005},
 issn = {0004-5411},
 pages = {365--473},
 numpages = {109},
 url = {http://doi.acm.org/10.1145/1066100.1066102},
 doi = {10.1145/1066100.1066102},
 acmid = {1066102},
 publisher = {ACM},
 address = {New York, NY, USA},
 keywords = {Theorem proving, decision procedures, program checking},
}

 The important part describing the merge and its undo is described in section 7 - The E-graph in Detail

 The following changes have been made to the merge algorithm:
 Old signatures are no longer removed from the table of signatures (also they now don't have to be reinserted back in undo)
 This means that the table can grow in memory but we can skip the whole 5.2 from the merge, so we save one whole pass through the parents.

*********************************************************************/


#include "Egraph.h"
#include "EgraphModelBuilder.h"
#include "Enode.h"
#include "TreeOps.h"
#include "Deductions.h"
#include "ModelBuilder.h"


static SolverDescr descr_uf_solver("UF Solver", "Solver for Quantifier Free Theory of Uninterpreted Functions with Equalities");

const char* Egraph::s_val_prefix = "u";
const char* Egraph::s_const_prefix = "n";
const char* Egraph::s_any_prefix = "a";
const char* Egraph::s_val_true = "true";
const char* Egraph::s_val_false = "false";

Egraph::Egraph(SMTConfig & c, Logic & l) : Egraph(c,l,ExplainerType::CLASSIC) {}

Egraph::Egraph(SMTConfig & c, Logic & l, ExplainerType explainerType)
      : TSolver            (descr_uf_solver, descr_uf_solver, c)
      , logic              (l)
      , enode_store        ( logic )
      , fa_garbage_frac    ( 0.5 )
      , values             ( nullptr )
{
    auto rawExplainer = [this](ExplainerType type) -> Explainer * {
        switch(type) {
            case ExplainerType::CLASSIC: {
                return new Explainer(enode_store);
            }
            case ExplainerType::INTERPOLATING: {
                return new InterpolatingExplainer(enode_store);
            }
            default: {
                return new Explainer(enode_store);
            }
        }
    }(explainerType);
    explainer.reset(rawExplainer);
}

//
// Pushes a backtrack point
//
void Egraph::pushBacktrackPoint( )
{
  // Save solver state if required
  backtrack_points.push( undo_stack_main.size( ) );

  TSolver::pushBacktrackPoint();
}

//
// Pops a backtrack point
//
void Egraph::popBacktrackPoint() {
//    opensmt::StopWatch sw(tsolver_stats.egraph_backtrack_timer);
    assert( backtrack_points.size( ) > 0 );
    size_t undo_stack_new_size = backtrack_points.last();
    backtrack_points.pop();
    backtrackToStackSize( undo_stack_new_size );

    // Restore deduction next
    TSolver::popBacktrackPoint();
}

//
// Returns a suggestion
//
PTRef Egraph::getSuggestion( )
{
  // Communicate suggestion
  while ( suggestions.size() != 0 )
  {
    PTRef tr = suggestions.last();
    suggestions.pop();
    if ( hasPolarity(tr) )
      continue;
    return tr;
  }

  // We have already returned all
  // the possible suggestions
  return PTRef_Undef;
}

lbool Egraph::getPolaritySuggestion(PTRef p)
{
    if (!isInformed(p)) { return l_Undef; }
    // MB: it could be uninterpreted predicate! No suggestion in that case
    if (!logic.isEquality(p) && !logic.isDisequality(p)) { return l_Undef; }
    bool equality = logic.isEquality(p);
    Pterm const & term = logic.getPterm(p);
    if (term.size() > 2) { return l_Undef; } // For now focus on 2 arguments
    PTRef lhs = term[0];
    PTRef rhs = term[1];
    assert(enode_store.has(lhs) && enode_store.has(rhs));
    if (!enode_store.has(lhs) || !enode_store.has(rhs)) { return l_Undef; }
    ERef e_lhs = termToERef(lhs);
    ERef e_rhs = termToERef(rhs);
    if (getEnode(e_lhs).getRoot() == getEnode(e_rhs).getRoot()) {
        // Already in the same equivalence class, avoid conflict
        return equality ? l_True : l_False;
    }
    Expl tmp;
    bool res = unmergeable(getEnode(e_lhs).getRoot(), getEnode(e_rhs).getRoot(), tmp);
    if (res) {
        // they are unmergable so don't assert equality
        return equality ? l_False : l_True;
    }
    // no decision
    return l_Undef;
}

//
// Communicate conflict
//
void Egraph::getConflict(vec<PtAsgn> & conflict)
{
    for (PtAsgn lit : explanation) {
        conflict.push(lit);
    }
#ifdef STATISTICS
    if (deduction) {
        if (cnfl.size() > tsolver_stats.max_reas_size)
            tsolver_stats.max_reas_size = cnfl.size();
        if (cnfl.size() < tsolver_stats.min_reas_size)
            tsolver_stats.min_reas_size = cnfl.size();
        tsolver_stats.reasons_sent ++;
        tsolver_stats.avg_reas_size += cnfl.size();
    }
    else {
        if (cnfl.size() > tsolver_stats.max_conf_size)
            tsolver_stats.max_conf_size = cnfl.size();
        if (cnfl.size() < tsolver_stats.min_conf_size)
            tsolver_stats.min_conf_size = cnfl.size();
        tsolver_stats.conflicts_sent ++;
        tsolver_stats.avg_conf_size += cnfl.size();
    }
#endif
}

void Egraph::clearModel()
{
    values.reset(nullptr);
}

void Egraph::computeModel( )
{
    if (values != nullptr)
        return;

    values = std::make_unique<Values>();
    for (ERef er : enode_store.getTermEnodes()) {
        ERef root_r = enode_store[er].getRoot();
        values->addValue(er, root_r);
    }
}

void Egraph::fillTheoryFunctions(ModelBuilder & modelBuilder) const
{
    EgraphModelBuilder(*this).fill(modelBuilder);
}

void Egraph::declareAtom(PTRef atom) {
    if (!enode_store.needsEnode(atom)) { return; }
    if (isInformed(atom)) { return; }
    declareTermRecursively(atom);
    setInformed(atom);
}

void Egraph::declareTermRecursively(PTRef tr) {
    if (declared.find(tr) != declared.end()) { return; } // already declared
    const Pterm& term = logic.getPterm(tr);
    // declare first the childen and then the current term
    assert(not logic.isIte(tr));
    for (PTRef child : term) {
        declareTermRecursively(child);
    }

    if (enode_store.needsEnode(tr)) {
        // Only mark as declared if declareTerm actually declared the term.  This is important since whether
        // tr needs an enode could change after incremental calls in surprising ways as a result of simplifications.
        declareTerm(tr);
        declared.insert(tr);
    }
}

/**
 * Adds the term to the solver taking into account the arguments.
 *
 * For the Boolean terms (that appear as arguments in UF), we add also
 * their negations.  This means that we need the negation uninterpreted
 * function.  In this Boolean case we add that a term is not equal to
 * its negation, with the reason true.
 *
 * @param tr
 */
void Egraph::declareTerm(PTRef tr) {
    assert(enode_store.needsEnode(tr));

    auto PTRefERefPairVec = enode_store.constructTerm(tr);

    if (PTRefERefPairVec.size() == 0) {
        return;
    }

    for (auto [term, eref] : PTRefERefPairVec) {
        updateUseVectors(term); (void)eref;
    }

    if (logic.hasSortBool(tr) and not logic.isDisequality(tr) and PTRefERefPairVec.size() == 2) {
        auto [negated_tr, negated_er] = PTRefERefPairVec[1];
        assert(logic.isNot(negated_tr));
        negatedTermToERef.insert(negated_tr, negated_er);
        assert(PTRefERefPairVec[0].tr == logic.mkNot(PTRefERefPairVec[1].tr));
        assertNEq(PTRefERefPairVec[0].er, PTRefERefPairVec[1].er, Expl(Expl::Type::pol, PtAsgn_Undef, PTRefERefPairVec[0].tr));
    }

    if (logic.hasSortBool(tr)) {
        setKnown(tr);
    }
}

bool Egraph::addEquality(PtAsgn pa) {
    Pterm const & pt = logic.getPterm(pa.tr);
    assert(pt.size() == 2);
    bool res = true;
    PTRef e = pt[0];
    for (int i = 1; i < pt.size() && res; i++)
        res = assertEq(e, pt[i], pa);

    if (res) {
        bool res2;
        // First: I'm not sure this is the right way to do this!
        // second:
        //  pa.sgn == true if this is an equality literal and false if this
        //  is a distinct
        if (pa.sgn == l_True)
            res2 = addTrue(pa.tr);
        else
            res2 = addFalse(pa.tr);

        if (!res2)
            return false;
    }

#ifdef STATISTICS
    if (res == false)
        tsolver_stats.unsat_calls++;
    // The sat_calls is increased already in addTrue
#endif

    return res;
}

bool Egraph::addDisequality(PtAsgn pa) {
    Pterm const & pt = logic.getPterm(pa.tr);
    bool res = true;

    if (pt.size() == 2)
        res = assertNEq(pt[0], pt[1], Expl(Expl::Type::std, pa, PTRef_Undef));
    else
        res = assertDist(pa.tr, pa);

#ifdef ENABLE_DIST_BOOL // This should be more efficient but osmt1 does not do it
    if (res == true)
#else
    if (res && pt.size() == 2)
#endif
    {
        bool res2;
        // pa.sgn == true if this is a disequality
        if (pa.sgn == l_True)
            res2 = addTrue(pa.tr);
        else
            res2 = addFalse(pa.tr);
        if (!res2)
            return false;
    }
#ifdef STATISTICS
    if (!res)
        tsolver_stats.unsat_calls++;
    // The sat_calls is increased already in addFalse
#endif

    return res;
}

bool Egraph::addTrue(PTRef term) {
    assert(logic.hasSortBool(term));
    assert(not logic.isNot(term));
    bool res = assertEq(term, logic.getTerm_true(), PtAsgn(term, l_True));
    if (res and negatedTermToERef.has(logic.mkNot(term))) {
        res = assertEq(logic.mkNot(term), logic.getTerm_false(), PtAsgn(term, l_True));
    }
#ifdef STATISTICS
    if (res == false)
        tsolver_stats.unsat_calls++;
    else {
        tsolver_stats.sat_calls++;
    }
#endif
    return res;
}

bool Egraph::addFalse(PTRef term) {
    assert(logic.hasSortBool(term));
    assert(not logic.isNot(term));
    bool res = assertEq(term, logic.getTerm_false(), PtAsgn(term, l_False));
    if (res and negatedTermToERef.has(logic.mkNot(term))) {
        res = assertEq(logic.mkNot(term), logic.getTerm_true(), PtAsgn(term, l_False));
    }
#ifdef STATISTICS
    if (res == false)
        tsolver_stats.unsat_calls++;
    else {
        tsolver_stats.sat_calls++;
    }
#endif
    return res;
}

//===========================================================================
// Private Routines for Core Theory Solver

//
// Assert an equality between nodes x and y
//
bool Egraph::assertEq ( PTRef tr_x, PTRef tr_y, PtAsgn r ) {
    ERef x = termToERef(tr_x);
    ERef y = termToERef(tr_y);
    return assertEq(x, y, r);
}

bool Egraph::assertEq(ERef x, ERef y, PtAsgn r) {
    assert(pending.size() == 0);
    pending.push({x, y});
    return mergeLoop(r);
}

//
// Merge what is in pending and propagate to parents
//
bool Egraph::mergeLoop( PtAsgn reason )
{
    bool congruence_pending = false;

    while ( pending.size() != 0 ) {
        // Remove a pending equivalence
        auto [p, q] = pending.last();
        pending.pop();
        Enode const & en_p = getEnode(p);
        Enode const & en_q = getEnode(q);

        if ( en_p.getRoot( ) == en_q.getRoot( ) )
            continue;

        // Store explanation, for either congruence or eq
        // The third argument is the reason for the merge
        // of p and q; they may merge because of an equality,
        // and in that case the reason is the id of the equality.
        // Or they may merge because of congruence, and in that
        // case the reason is empty (NULL). Notice that we store
        // reasons only among TERMs, and never among LISTs. That
        // means that the reason for p and q being equal has to
        // be found recursively in their arguments. We store the
        // reason even in case of unmergability, to have an
        // automatic way of retrieving a conflict.

        explainer->storeExplanation( p, q, congruence_pending ? PtAsgn(PTRef_Undef, l_Undef) : reason );

        // Check if they can't be merged
        Expl reason_inequality;
        bool res = unmergeable( en_p.getRoot(), en_q.getRoot(), reason_inequality );

        // They are not unmergable, so they can be merged
        if ( !res ) {
            merge( en_p.getRoot( ), en_q.getRoot( ), reason );
            congruence_pending = true;
            continue;
        }
        // Conflict detected. We should retrieve the explanation
        // We have to distinguish 2 cases. If the reason for the
        // conflict is ERef_Undef, it means that a conflict arises because
        // we tried to merge two classes that are assigned to different
        // constants, otherwise we have a proper reason
        has_explanation = true;
        ERef reason_1 = ERef_Undef;
        ERef reason_2 = ERef_Undef;

        ERef enr_proot = en_p.getRoot();
        ERef enr_qroot = en_q.getRoot();

        if ( reason_inequality.type == Expl::Type::cons) {
            // Different constants
            explainConstants(p,q);
        }
        // Does the reason term correspond to disequality symbol
        else if (reason_inequality.type == Expl::Type::std) {
            PtAsgn pta = reason_inequality.pta;
            if ( logic.getPterm(pta.tr).size() > 2 ) {
                // A distinction.
                // We should iterate through the elements of the distinction
                // and find which atoms are causing the conflict
                Pterm const & pt_reason = logic.getPterm(pta.tr);
                for (auto ptr_arg : pt_reason) {
                    // (1) Get the enode corresponding to the proper term
                    // (2) Find the enode corresponding to the root
                    // (3) Check if the root enode is the same as the root of p or q

                    ERef  enr_arg = enode_store.getERef(ptr_arg);             // (1)
                    ERef  enr_arg_root = enode_store[enr_arg].getRoot();      // (2)

                    // (3)
                    if ( enr_arg_root == enr_proot ) { reason_1 = enr_arg; }
                    if ( enr_arg_root == enr_qroot ) { reason_2 = enr_arg; }
                }
                assert( reason_1 != ERef_Undef );
                assert( reason_2 != ERef_Undef );
                doExplain(reason_1, reason_2, reason_inequality.pta);
            } else if ( logic.isEquality(reason_inequality.pta.tr) ) {
                // The reason is a negated equality
                assert(reason_inequality.pta.sgn == l_False);
                Pterm const & pt_reason = logic.getPterm(reason_inequality.pta.tr);

                // The equality
                // If properly booleanized, the left and righ sides of equality
                // will always be UF terms
                // The left hand side of the equality
                reason_1 = enode_store.getERef(pt_reason[0]);
                // The rhs of the equality
                reason_2 = enode_store.getERef(pt_reason[1]);

                assert( reason_1 != ERef_Undef );
                assert( reason_2 != ERef_Undef );
                doExplain(reason_1, reason_2, reason_inequality.pta);
            } else if ( logic.isUP(reason_inequality.pta.tr) ) {
                // The reason is an uninterpreted predicate
                assert(false);
                explanation.push(reason_inequality.pta);
            }
        } else if (reason_inequality.type == Expl::Type::pol) {
            // The reason is fundamentally that x and (not x) would go to the same eq class
            ERef pos = enode_store.getERef(reason_inequality.pol_term);
            ERef neg = enode_store.getERef(logic.mkNot(reason_inequality.pol_term));
            doExplain(neg, pos, {logic.getTerm_false(), l_True});
        }
        // Clear remaining pendings
        pending.clear( );
        // Remove the last explanation that links
        // the two unmergable classes
        explainer->removeExplanation();
//        expCleanup(); // called in expExplain(r1, r2)
        // Return conflict
        return false;
    }
    return true;
}

//
// Assert a disequality between nodes x and y
//
bool Egraph::assertNEq ( PTRef x, PTRef y, const Expl &r ) {
#ifdef GC_DEBUG
    checkRefConsistency();
    assert(r.sgn != l_Undef);
    cerr << "Asserting distinction of " << logic.printTerm(x)
         << " and " << logic.printTerm(y)
         << " enforced by " << (r.sgn == l_True ? "" : "not ")
         << logic.printTerm(r.tr) << endl;
#endif
    checkFaGarbage();
#ifdef GC_DEBUG
    checkRefConsistency();
#endif
#if MORE_DEDUCTIONS
    neq_list.push_back( r );
    undo_stack_oper.push_back( ASSERT_NEQ );
    undo_stack_term.push_back( r );
#endif

    ERef xe = enode_store.getERef(x);
    ERef ye = enode_store.getERef(y);
    ERef p = getEnode(xe).getRoot();
    ERef q = getEnode(ye).getRoot();
    // They can't be different if the nodes are in the same class
    if ( p == q ) {
        doExplain(xe, ye, r.pta);
        return false;
    }
    return assertNEq(p, q, r);
}

bool Egraph::assertNEq(ERef p, ERef q, Expl const & r)
{
    // Is it possible that x is already in the list of y
    // and viceversa ? YES. If things have
    // been done carefully (for instance, if x=y is the same atom
    // as y=x), each theory atom appears only once in the trail.
    // However it is possible to get x!=y and x<y, and pushing
    // x<y is the same as x!=y for the UF solver. However, I don't
    // think this is going to be a big performance problem, worst
    // case it doubles the size of forbid lists. But checking the
    // lists for duplicates every time would be time-consuming,
    // especially when we have many !='s. For now I'll leave it
    // unchecked.

    // Create new distinction in q
    // If this is the first distinction for q, make it a "special" one,
    // so that it has the owner reference.  Allocate an extra 32 bits.
    // If there is no node in forbid list
    ELRef pdist = ELRef_Undef;
    if (Enode & en_q = getEnode(q); en_q.getForbid() == ELRef_Undef) {
        pdist = forbid_allocator.alloc(p, r, q);
        en_q.setForbid( pdist );
        forbid_allocator[pdist].link = pdist;
#ifdef GC_DEBUG
        checkRefConsistency();
#endif
    }

    // Otherwise we should put the new node after the first
    // and make the first point to pdist. This is because
    // the list is circular, but could be empty. Therefore
    // we need a "reference" element for keeping it circular.
    // So the last insertion is either the second element or
    // the only present in the list
    else {
        pdist = forbid_allocator.alloc(p, r, ERef_Undef);
        forbid_allocator[pdist].link = forbid_allocator[en_q.getForbid()].link;
        forbid_allocator[en_q.getForbid()].link = pdist;
#ifdef GC_DEBUG
        cerr << "Added distinction " << pdist.x << endl;
        cerr << printDistinctionList(en_q.getForbid(), forbid_allocator);
        checkRefConsistency();
#endif
    }

    // Create new distinction in p
    ELRef qdist = ELRef_Undef;
    if (Enode & en_p = getEnode(p); en_p.getForbid() == ELRef_Undef ) {
        qdist = forbid_allocator.alloc(q, r, p);
        en_p.setForbid( qdist );
        forbid_allocator[qdist].link = qdist;
#ifdef GC_DEBUG
        checkRefConsistency();
#endif
    }
    // Same arguments above
    else {
        qdist = forbid_allocator.alloc(q, r, ERef_Undef);
        forbid_allocator[qdist].link = forbid_allocator[en_p.getForbid()].link;
        forbid_allocator[en_p.getForbid()].link = qdist;
#ifdef GC_DEBUG
        cerr << "Added distinction " << qdist.x << endl;
        cerr << printDistinctionList(en_p.getForbid(), forbid_allocator);
        checkRefConsistency();
#endif
    }
    // Save operation in undo_stack
    undo_stack_main.push( Undo(DISEQ, q) );
    return true;
}

// Assert a distinction on arguments of tr_d

bool Egraph::assertDist( PTRef tr_d, PtAsgn tr_r )
{
    assert(tr_d == tr_r.tr);

    // Retrieve distinction number
    auto index = enode_store.getDistIndex(tr_d);
    // While asserting, check that no two nodes are congruent
    Map<ERef, ERef, ERefHash> root_to_enode;
    // Changed nodes recorded here for undoing the distinction in case of conflict
    vec<ERef> nodes_changed;
    // Assign distinction flag to all arguments
    const Pterm& pt_d = logic.getPterm(tr_d);

    ERef inConflict = ERef_Undef;

    for (PTRef tr_c : pt_d) {
        ERef er_c = enode_store.getERef(tr_c);
        ERef root = getEnode(er_c).getRoot();
        if (root_to_enode.has(root)) {
            // Two equivalent nodes in the same distinction. Conflict
            inConflict = er_c;
            break;
        }
        assert(not root_to_enode.has(root));
        root_to_enode.insert(root, er_c);

        // Activate distinction in e
        // This should be done for the root of en_c, not en_c
        getEnode(root).addDistClass(index);
        nodes_changed.push(root);
    }

    if (inConflict != ERef_Undef) {
        // Extract the other node with the same root
        Enode const & en_c = getEnode(inConflict);
        ERef root = en_c.getRoot();
        ERef p = root_to_enode[root];
        assert(getEnode(p).getRoot() == en_c.getRoot());
        // Retrieve explanation
        doExplain(inConflict, p, tr_r);
        // Revert changes, as the current context is inconsistent
        for (ERef n : nodes_changed) {
            // Deactivate distinction in n
            getEnode(n).clearDistClass(index);
        }
        return false;
    }
    assert(inConflict == ERef_Undef);
    // Distinction pushed without conflict
    undo_stack_main.push(Undo(DIST, tr_d));
    return true;
}

void Egraph::undoDistinction(PTRef tr_d) {
    auto index = enode_store.getDistIndex(tr_d);
    Pterm const & pt_d = logic.getPterm(tr_d);
    for (PTRef tr_c : pt_d) {
        getEnode(enode_store.getERef(tr_c)).clearDistClass(index);
    }
}

//
// Backtracks stack to a certain size
//
void Egraph::backtrackToStackSize ( size_t size ) {
    // Make sure explanation is cleared
    // (might be empty, though, if boolean backtracking happens)
    explanation.clear();
    has_explanation = false;

    //
    // Restore state at previous backtrack point
    //
//    printf("stack size %d > %d\n", undo_stack_term.size(), size);
    while (undo_stack_main.size_() > size) {
        Undo u = undo_stack_main.last();
        oper_t last_action = u.oper;

        undo_stack_main.pop();

        switch (last_action) {
            case MERGE: {
                ERef e = u.arg.er;
                undoMerge(e);
                explainer->removeExplanation();
                break;
            }
#if MORE_DEDUCTIONS
            case ASSERT_NEQ: {
                ERef e = u.arg.er;
                assert( neq_list.last( ) == e );
                neq_list.pop( );
                break;
            }
#endif
            case DISEQ: {
                ERef e = u.arg.er;
                undoDisequality(e);
                break;
            }
            case DIST: {
                PTRef ptr = u.arg.ptr;
                undoDistinction(ptr);
                break;
            }
            case CONS: {
                break;
            }
            case SET_POLARITY: {
                assert(hasPolarity(u.arg.ptr));
                clearPolarity(u.arg.ptr);
                break;
            }
            default: {
                opensmt_error("unknown action");
                break;
            }
        }
    }
}


//=============================================================================
// Congruence Closure Routines

//
// Merge the class of x with the class of y
// x will become the representative
//
void Egraph::merge ( ERef x, ERef y, PtAsgn reason )
{
#ifdef GC_DEBUG
    checkRefConsistency();
    checkForbidReferences(x);
    checkForbidReferences(y);
#endif
    { // sanity checks
        assert(getEnode(x).getRoot() != getEnode(y).getRoot());
        assert(x == getEnode(x).getRoot());
        assert(y == getEnode(y).getRoot());
    }

    // Step 1: Ensure that the constant or the one with a larger equivalence
    // class will be in x (and will become the root). Constants must be roots! It is an invariant that other code depends on!
    if (isConstant(y) || (!(isConstant(x)) && (getParentsSize(x) < getParentsSize(y)))) {
        std::swap(x,y);
    }

    // MB: Before we actually merge the classes, we check if we are not merging with eq. class of constant True or False
    deduce( x, y, reason );

    Enode & en_x = getEnode(x);
    Enode const & en_y = getEnode(y);

    assert(not isConstant(y));

    // Step 2: Propagate equalities to other ordinary theories
    // MB: We are not doing that
    // Step 3: MB: Also not relevant for us

    // Step 4: Update forbid list for x by adding elements of y
    mergeForbidLists(x, en_y);
#ifdef GC_DEBUG
    checkRefConsistency();
    checkForbidReferences(x);
#endif
    // Step 4: Merge distinction classes
    mergeDistinctionClasses(en_x, en_y);

    // Step 5: Consists of several operations

    // Step 5.2: Remove old signatures of y’s class’s parents and remove parents of y from other use vectors
    processParentsBeforeMerge(y);

    // Step 5.3: Union of equivalence classes
    mergeEquivalenceClasses(x, y);

    // Step 5.5: Insert new signatures and propagate congruences
    processParentsAfterMerge(y);

    // Step 6: Merge parent lists -> done in 5.5
    // Step 7: Not relevant -> skipped

    // Step 8: Push undo record
    undo_stack_main.push( Undo(MERGE,y) );
}

//
// Deduce facts from the merge of x and y
//
// Currently, it only deduces if something we are merging into eq. class of a constant True or False
void Egraph::deduce( ERef x, ERef y, PtAsgn reason ) {
    lbool deduced_polarity = l_Undef;

    // Depends on the invariant that constants are always the root of its eq. class.
    // Also we assume that y is root of the class being merged into class with root x
    // That means only x can be constant.
    assert(y != enode_store.getEnode_true() && y != enode_store.getEnode_false());
    if ( x == enode_store.getEnode_true() ){
        deduced_polarity = l_True;
    }
    else if ( x == enode_store.getEnode_false() ){
        deduced_polarity = l_False;
    }

    if ( deduced_polarity == l_Undef ) {
#ifdef NEG_DEDUCE
        // Work on negative deductions:
        // Merge of x and y results in inequalities expressed in the forbid
        // lists.  It would make sense to propagate these inequalities to the
        // SAT solver so that it would not need to figure them out one by one.
        // This is an attempt to proagate this information as well.
        ELRef elr = enode_store[x].getForbid();
        if (elr == ELRef_Undef) return; // Nothing to be done
        ELRef c_elr = elr;
        while (true) {
            const Elist& el = forbid_allocator[c_elr];
            ELRef next_elr = el.link;
            const Elist el_o = forbid_allocator[next_elr];
            PTRef z = enode_store[el_o.e].getTerm();

            vec<ERef> two_terms;
            two_terms.push(x);
            two_terms.push(y);
            // repeat for both x and y:
            for (int i = 0; i < 2; i++) {
                // x != z.  Do we have a term for this?
                vec<PTRef> args;
                args.push(enode_store[two_terms[i]].getTerm());
                args.push(z);

                // Is there a literal for this fact?
                PTRef eq = logic.hasEquality(args);
                if (eq != PTRef_Undef && enode_store.termToERef.has(eq)) {
                    // Found the equality, and we deduce its negation
                    ERef ded_eq = enode_store.termToERef[eq];
                    enode_store[ded_eq].setDeduced(l_False);
                    deductions.push(PtAsgn_reason(eq, l_False, reason.tr));
                    tsolver_stats.deductions_done ++;
                }
            }
            if (elr == next_elr) break;
            c_elr = next_elr;
        }
#endif // NEG_DEDUCE
        return;
    }
    // x is the constant, go over the members of eq class of y and check if they have can be propagated to SAT solver
    ERef v = y;
    const ERef vstart = v;
    for (;;) {
        // We deduce only things that aren't currently assigned or
        // that we previously deduced on this branch
        PTRef v_tr = getEnode(v).getTerm();
        if (not hasPolarity(v_tr) and not logic.isNot(v_tr)) {
            // Negated boolean terms are handled in the positive case
            assert(v_tr == enode_store.getPTRef(v));
            storeDeduction(PtAsgn_reason(v_tr, deduced_polarity, reason.tr));
#ifdef STATISTICS
            tsolver_stats.deductions_done ++;
#endif
        }
        v = getEnode(v).getEqNext();
        if (v == vstart)
            break;
    }
}

//
// Starts with the E-graph state that existed after the
// pertinent merge and restores the E-graph to the state
// it had before the pertinent merge
//
void Egraph::undoMerge( ERef y )
{
#ifdef GC_DEBUG
    checkRefConsistency();
#endif
    assert( y != ERef_Undef );
    Enode const & en_y = enode_store[y];

    // x is the node that was merged with y
    ERef x = en_y.getRoot( );
    assert( x != ERef_Undef );

    Enode & en_x = enode_store[x];

    // Undo Step 6 of merge:
//    unmergeParentLists(en_x, en_y);

    // Undo Step 5 of merge
    // Undo Case 2 of Step 5.5 of merge
    processParentsBeforeUnMerge(y);

    // Undo Step 5.4 of merge
    // Undo Step 5.3 of merge
    unmergeEquivalenceClasses(x, y);

    // Undo Case 1 of Step 5.5 of merge
    // Since we are skipping Step 5.2 in merge. we do not have to undo that.
//    unmergeParentCongruenceClasses(w);
    // re-insert parents of y
    processParentsAfterUnMerge(y);

    // Undo step 4 of Merge
    unmergeDistinctionClasses(en_x, en_y);
    unmergeForbidLists(x, en_y);

    // Undo Step 2 -> not relevant
#ifdef GC_DEBUG
    checkRefConsistency();
#endif
}

//
// Restore the state before the addition of a disequality
//
void Egraph::undoDisequality(ERef x)
{
#ifdef GC_DEBUG
    checkRefConsistency();
#endif
    Enode & en_x = getEnode(x);
    assert( en_x.getForbid() != ELRef_Undef );

    // We have to distinguish two cases:
    // If there is only one node, that is the
    // distinction to remove
    ELRef xfirst = en_x.getForbid( );
    ERef y = ERef_Undef;
    Elist & el_xfirst = forbid_allocator[xfirst];
    if ( el_xfirst.link == xfirst )
        y = el_xfirst.e;
    else
        y = forbid_allocator[el_xfirst.link].e;

    Enode& en_y = enode_store[y];


    ELRef yfirst = en_y.getForbid();

#ifdef GC_DEBUG
    cerr << "Distinction list for xfirst" << endl;
    cerr << printDistinctionList(xfirst, forbid_allocator);
    cerr << "Distinction list for yfirst" << endl;
    cerr << printDistinctionList(yfirst, forbid_allocator);
#endif

    // Some checks
    assert( yfirst != ELRef_Undef );
    Elist & el_yfirst = forbid_allocator[yfirst];
    assert( el_yfirst.link != yfirst || el_yfirst.e == x );
    assert( el_yfirst.link == yfirst || forbid_allocator[el_yfirst.link].e == x );
    assert( en_x.getRoot( ) != en_y.getRoot( ) );

    ELRef ydist = el_xfirst.link == xfirst ? xfirst : el_xfirst.link;
    Elist const & el_ydist = forbid_allocator[ydist];

    // Only one node in the list
    if ( el_ydist.link == ydist ) {
        forbid_allocator.removeRef(x, en_x.getForbid());
        en_x.setForbid( ELRef_Undef );
    }
    // Other nodes in the list
    else
        el_xfirst.link = el_ydist.link;

    forbid_allocator.free(ydist);

    ELRef xdist = el_yfirst.link == yfirst ? yfirst : el_yfirst.link;
    Elist const & el_xdist = forbid_allocator[xdist];

    // Only one node in the list
    if ( el_xdist.link == xdist ) {
        assert(en_y.getForbid() != ELRef_Undef);
        forbid_allocator.removeRef(y, en_y.getForbid());
        en_y.setForbid( ELRef_Undef );
    }
    // Other nodes in the list
    else
        el_yfirst.link = el_xdist.link;

    forbid_allocator.free(xdist);
#ifdef GC_DEBUG
    checkRefConsistency();
#endif
}


bool Egraph::unmergeable(ERef x, ERef y, Expl& r) const
{
    assert( x != ERef_Undef );
    assert( y != ERef_Undef );

    ERef p = getEnode(x).getRoot();
    ERef q = getEnode(y).getRoot();

    // If they are in the same class, they can merge
    if ( p == q ) return false;
    // Check if they have different constants. It is sufficient
    // to check that they both have a constant. It is not
    // possible that the constant is the same. In fact if it was
    // the same, they would be in the same class, but they are not
    // Check if they are part of the same distinction (general distinction)
    if (isConstant(p) && isConstant(q)) {
        r = Expl(Expl::Type::cons, PtAsgn_Undef, PTRef_Undef);
        return true;
    }
    Enode const & en_p = getEnode(p);
    Enode const & en_q = getEnode(q);

    if (dist_t intersection = en_p.getDistClasses() & en_q.getDistClasses()) {
        // Compute the first index in the intersection
        // TODO: Use index = std::countr_zero<unsigned>(intersection) when c++20 becomes available?
        unsigned index = 0;
        while ((intersection & 1) == 0) {
            intersection = intersection >> 1;
            ++index;
        }
        // Dist terms are all inequalities, hence their polarity's true
        PTRef ineq_tr = enode_store.getDistTerm(index);
        r = Expl(Expl::Type::std, {ineq_tr, l_True}, PTRef_Undef);
        return true;
    }
    // Check forbid lists (binary distinction)
    ELRef pstart = en_p.getForbid();
    ELRef qstart = en_q.getForbid();
    // If at least one is empty, they can merge
    if (pstart == ELRef_Undef || qstart == ELRef_Undef) {
        return false;
    }

    ELRef pptr = pstart;
    ELRef qptr = qstart;

    for (;;) {
        Elist const & el_pptr = forbid_allocator[pptr];
        Elist const & el_qptr = forbid_allocator[qptr];
        // They are unmergeable if they are on the other forbid list
        if (getEnode(el_pptr.e).getRoot() == q) {
            r = el_pptr.reason;
            assert((r.type == Expl::Type::pol) or ((logic.isEquality(r.pta.tr) and r.pta.sgn == l_False) or (logic.isDisequality(r.pta.tr) and r.pta.sgn == l_True)));
            return true;
        }
        if (getEnode(el_qptr.e).getRoot() == p) {
            r = el_qptr.reason;
            assert((r.type == Expl::Type::pol) or ((logic.isEquality(r.pta.tr) and r.pta.sgn == l_False) or (logic.isDisequality(r.pta.tr) and r.pta.sgn == l_True)));
            return true;
        }
        // Pass to the next element
        pptr = el_pptr.link;
        qptr = el_qptr.link;
        // If either list finishes, exit. This is ok because
        // if x is on y's forbid list, then y is on x's forbid
        // list as well
        if ( pptr == pstart ) break;
        if ( qptr == qstart ) break;
    }
    // If here they are mergable
    assert(r.type == Expl::Type::undef);
    return false;
}

bool Egraph::isEffectivelyEquality(PTRef tr) const {
    assert(enode_store.needsEnode(tr));
    return logic.isEquality(tr) and enode_store.needsRecursiveDefinition(tr);
}

bool Egraph::isEffectivelyDisequality(PTRef tr) const {
    assert(enode_store.needsEnode(tr));
    return logic.isDisequality(tr) and enode_store.needsRecursiveDefinition(tr);
}

bool Egraph::isEffectivelyUP(PTRef tr) const {
    assert(enode_store.needsEnode(tr));
    return not isEffectivelyEquality(tr) and not isEffectivelyDisequality(tr);
}

bool Egraph::assertLit(PtAsgn pta)
{
    // invalidate values
    lbool sgn = pta.sgn;
    PTRef pt_r = pta.tr;

    if (hasPolarity(pt_r) && getPolarity(pt_r) == sgn) {
        // Already known, no new information;
        // MB: The deductions done by this TSolver are also marked using polarity.
        //     The invariant is that TSolver will not process the literal again (when asserted from the SAT solver)
        //     once it is marked for deduction, so the implementation must count with that.
        tsolver_stats.sat_calls ++;
        return true;
    }

    bool res = true; // MB: true means NO conflict, false means conflict
    undo_stack_main.push(Undo(SET_POLARITY, pt_r));
    setPolarity(pt_r, sgn);

    // Issue185: In some cases equalities do not have a recursive definition.
    // They should be treated as UPs.
    if (isEffectivelyEquality(pt_r) && sgn == l_True) {
        res = addEquality(PtAsgn(pt_r, l_True));
    } else if (isEffectivelyEquality(pt_r) && sgn == l_False) {
        res = addDisequality(PtAsgn(pt_r, l_False));
    } else if (isEffectivelyDisequality(pt_r) && sgn == l_True) {
        res = addDisequality(PtAsgn(pt_r, l_True));
    } else if (isEffectivelyDisequality(pt_r) && sgn == l_False) {
        if (logic.getPterm(pt_r).size() != 2) {
            throw OsmtInternalException("Internal error: Negated distinct asserted to Egraph");
        }
        res = addEquality(PtAsgn(pt_r, l_False));
    } else if (isEffectivelyUP(pt_r) && sgn == l_True) {
        // MB: Short circuit evaluation is important, the second call should NOT happen if the first returns false
        res = addTrue(pt_r);
    } else if (isEffectivelyUP(pt_r) && sgn == l_False) {
        // MB: Short circuit evaluation is important, the second call should NOT happen if the first returns false
        res = addFalse(pt_r);
    } else {
        assert(false);
    }

    !res ? tsolver_stats.unsat_calls ++ : tsolver_stats.sat_calls ++;
    return res;
}

//=================================================================================================
// Garbage Collection methods:

void Egraph::relocAll(ELAllocator& to) {
    for (int i = 0; i < forbid_allocator.elists.size(); i++) {
        // Here er points to the old allocator
        ELRef er = forbid_allocator.elists[i];
#ifdef GC_DEBUG
        cerr << "Starting gc round " << i << endl;
#endif
        ELRef er_old = er;
        ELRef start = er;
        if (forbid_allocator[er].isDirty()) continue;
        if (forbid_allocator[er].reloced()) continue;
#ifdef GC_DEBUG
        cerr << printDistinctionList(er, forbid_allocator);
        do {
            Elist& e_old = forbid_allocator[er_old];
            for (int j = 0; j < forbid_allocator.referenced_by[e_old.getId()].size(); j++) {
                ERef referer = forbid_allocator.referenced_by[e_old.getId()][j];
                if (referer == ERef_Undef) continue;
                assert (e_old.e != referer);
            }

        } while (start != er_old);
        assert(start == er_old);
#endif
        ELRef prev_fx = ELRef_Undef;
        bool done = false;
        while (true) {
#ifdef GC_DEBUG
            cerr << "Traversing forbid list " << endl
                 << "  node: " << er.x
                 << "  link: " << forbid_allocator[er].link.x << endl
                 << "  ERef: " << forbid_allocator[er].e.x
                 << "  Reason: " <<
                    logic.printTerm(forbid_allocator[er].reason.tr)
                 << endl;
            if (enode_store[forbid_allocator[er].e].isTerm()) {
                cerr << "  Term: "
                     << logic.printTerm(enode_store[forbid_allocator[er].e].getTerm()) << endl;
            }
#endif
            forbid_allocator.reloc(er, to);
            // Now er points to the new allocator
#ifdef GC_DEBUG
            cerr << "  new node: " << er.x << endl;
#endif
            // er_old points to the old allocator
            auto id = to[er].getId();
            for (ERef o : to.referenced_by[id]) {
#ifdef GC_DEBUG
                cerr << "Updating owner references" << endl;
#endif
                assert(o != ERef_Undef);
                enode_store[o].setForbid(er);
#ifdef GC_DEBUG
                assert(to[er].getId() == to[enode_store[o].getForbid()].getId());
#endif
            }
            if (prev_fx != ELRef_Undef)
                to[prev_fx].link = er;
            if (done) break;
            prev_fx = er;
            er = forbid_allocator[er_old].link;
#ifdef GC_DEBUG
            cerr << "Now going to node " << er.x << endl;
#endif
            er_old = er;
            if (er == start) done = true;
        }
#ifdef GC_DEBUG
        cerr << "End of gc round " << i << endl;
        cerr << printDistinctionList(er, to);

        ELRef start_old;
        ELRef start_new;
        ELRef er_new;
        start_old = er_old = start;
        start_new = er_new = forbid_allocator[er_old].rel_e;
        do {
            Elist& e_old = forbid_allocator[er_old];
            Elist& e_new = to[er_new];

            assert(e_old.isDirty() == e_new.isDirty());
            assert(e_new.isDirty() == false);
            assert(e_old.reason.tr == e_new.reason.tr);
            // TODO MB: next 3 lines there is some legacy code that does not compile anymore. Rewrite or remove!
//            ERef reason_lhs = enode_store.termToERef[term_store[e_new.reason.tr][0]];
//            ERef reason_rhs = enode_store.termToERef[term_store[e_new.reason.tr][1]];
//            assert (enode_store[reason_lhs].getRoot() != enode_store[reason_rhs].getRoot());
            for (int j = 0; j < to.referenced_by[to[er_new].getId()].size(); j++) {
                ERef referer = to.referenced_by[to[er_new].getId()][j];
                if (referer == ERef_Undef) continue;
                assert (to[er_new].e != referer);
            }
            er_old = forbid_allocator[er_old].link;
            er_new = to[er_new].link;

        } while (start_old != er_old);
        assert(start_new == er_new);

#endif
    }
}

void Egraph::faGarbageCollect() {
    ELAllocator to(forbid_allocator.size() - forbid_allocator.wasted());
#ifdef GC_DEBUG
    checkRefConsistency();
#endif
    relocAll(to);
    if (config.verbosity() >= 10)
        printf("Garbage collection:   %12d bytes => %12d bytes|\n",
               forbid_allocator.size()*ELAllocator::Unit_Size, to.size()*ELAllocator::Unit_Size);
    to.moveTo(forbid_allocator);
#ifdef GC_DEBUG
    checkRefConsistency();
#endif
}

void Egraph::mergeForbidLists(ERef toRef, const Enode & from) {
    Enode & to = getEnode(toRef);
    if ( from.getForbid( ) != ELRef_Undef ) {
        if ( to.getForbid( ) == ELRef_Undef ) {
            // We assign the same forbid list
            to.setForbid( from.getForbid( ) );
            forbid_allocator.addReference(to.getForbid(), toRef);
        } else {
            // Otherwise we splice the two lists
            ELRef tmp = forbid_allocator[to.getForbid()].link;
            forbid_allocator[to.getForbid()].link = forbid_allocator[from.getForbid()].link;
            forbid_allocator[from.getForbid()].link = tmp;
        }
    }
}

void Egraph::mergeDistinctionClasses(Enode & to, const Enode & from) {
    to.setDistClasses( ( to.getDistClasses( ) | from.getDistClasses( ) ) );
}

void Egraph::unmergeDistinctionClasses(Enode & to, const Enode & from) {
    to.setDistClasses( ( to.getDistClasses() & ~(from.getDistClasses())) );
}

void Egraph::mergeEquivalenceClasses(ERef newroot, ERef oldroot) {
    // Perform the union of the two equivalence classes
    // i.e. reroot every node in y's class to point to x
    ERef v = oldroot;
    ERef vstart = v;
    while (true) {
        Enode & en_v = getEnode(v);
        en_v.setRoot(newroot);
        v = en_v.getEqNext();
        if (v == vstart)
            break;
    }

    // Splice next lists
    Enode & en_x = getEnode(newroot);
    Enode & en_y = getEnode(oldroot);
    ERef tmp = en_x.getEqNext();
    en_x.setEqNext(en_y.getEqNext());
    en_y.setEqNext(tmp);
    // Update size of the congruence class
    en_x.setEqSize(en_x.getEqSize() + en_y.getEqSize());
}

void Egraph::unmergeEquivalenceClasses(ERef newroot, ERef oldroot) {
    Enode & en_x = getEnode(newroot);
    Enode & en_y = getEnode(oldroot);
    // Restore the size of x's class
    en_x.setEqSize(en_x.getEqSize() - en_y.getEqSize());
    // Unsplice next lists
    ERef tmp = en_x.getEqNext();
    en_x.setEqNext(en_y.getEqNext());
    en_y.setEqNext(tmp);
    // Reroot each node of y's eq class back to y
    ERef v = oldroot;
    ERef vstart = v;
    while (true) {
        Enode & en_v = getEnode(v);
        en_v.setRoot(oldroot);
        v = en_v.getEqNext();
        if (v == vstart)
            break;
    }
}

void Egraph::unmergeForbidLists(ERef toRef, const Enode & from) {
    Enode & to = getEnode(toRef);
    // Restore forbid list for x and y
    if ( (to.getForbid( ) == from.getForbid() ) && to.getForbid() != ELRef_Undef ) {
        forbid_allocator.removeRef(toRef, to.getForbid());
        to.setForbid( ELRef_Undef );
    }
    // Unsplice back the two lists
    else if ( from.getForbid( ) != ELRef_Undef ) {
        ELRef tmp = forbid_allocator[to.getForbid()].link;
        forbid_allocator[to.getForbid()].link = forbid_allocator[from.getForbid()].link;
        forbid_allocator[from.getForbid()].link = tmp;
    }
}



/**
 * Before oldroot is merged, the parents of its congruence class are scanned to
 * 1. Remove them from signature table
 * 2. Remove them from use-vectors of the other children (they are kept in the oldroot's use-vector for post-merge pass)
 */
void Egraph::processParentsBeforeMerge(ERef oldroot) {
    UseVector const & oldroot_parents = parents[getEnode(oldroot).getCid()];
    for (auto entry : oldroot_parents) {
        assert(not entry.isMarked());
        if (entry.isValid()) {
            ERef parent = UseVector::entryToERef(entry);
            enode_store.removeSig(parent);
            removeFromUseVectorsExcept(parent, getEnode(oldroot).getCid());
        }
    }
}

/**
   *
   * After merge, the parents of the merged root (oldroot) are scanned again to restore the invariants.
   * Their signature has changed after the merge.
   * Either i) there already is a term with the new signature, or ii) there is no term with the new signature.
   *
   * i) The parent is no longer a congruence root. This means there already is a representative in the signature table
   * and use-vectors. We only mark the parent in the old use-vector for backtracking and enqueue the discovered congruence.
   *
   * ii) There is no other representative with the new signature, so the parent remains a congruence root.
   * Since we removed it from signature table and use-vectors in processParentsBeforeMerge, we reintroduce it to both
   * data-structures. Note that the new signature will be used at this point.
   */
void Egraph::processParentsAfterMerge(ERef oldroot) {
    UseVector & oldroot_parents = parents[getEnode(oldroot).getCid()];
    for (auto & entry : oldroot_parents) {
        assert(!entry.isMarked());
        if (entry.isValid()) {
            ERef parent = UseVector::entryToERef(entry);
            ERef q = enode_store.lookupSig(parent);
            if (q != ERef_Undef) {
                // Case 1: p joins q's congruence class
                assert(q != parent);
                pending.push({parent, q});
                // p is no longer in the congruence table
                // put a mark for backtracking
                entry.mark();
            }
            else {
                // Case 2: p remains congruent root (but now has new signature)
                enode_store.insertSig(parent);
                addToUseVectors(parent);
            }
        }
    }
}

/**
 * Undoes the effect of processParentsAfterMerge
 */
void Egraph::processParentsBeforeUnMerge(ERef oldroot) {
    UseVector & oldroot_parents = parents[getEnode(oldroot).getCid()];
    for (auto & entry : oldroot_parents) {
        if (entry.isFree()) { continue; }
        if (entry.isValid()) {
            ERef parent = UseVector::entryToERef(entry);
            assert(enode_store.containsSig(parent));
            enode_store.removeSig(parent);
            removeFromUseVectors(parent);
        }
        else {
            assert(entry.isMarked());
            entry.unmark();
        }
    }
}

/**
 * Undoes the effect of processParentsBeforeMerge
 */
void Egraph::processParentsAfterUnMerge(ERef oldroot) {
    UseVector & oldroot_parents = parents[getEnode(oldroot).getCid()];
    for (auto it = oldroot_parents.begin(); it != oldroot_parents.end(); ++it) {
        if (it->isValid()) {
            ERef parent = UseVector::entryToERef(*it);
            enode_store.insertSig(parent);
            oldroot_parents.clearEntryAt(it - oldroot_parents.begin()); // required for reinserting for all children
            addToUseVectors(parent);
        }
    }
}

void Egraph::doExplain(ERef x, ERef y, PtAsgn reason_inequality) {
    explanation = explainer->explain(x,y);
#ifdef EXPLICIT_CONGRUENCE_EXPLANATIONS
    for (auto ptRefPair : explainer->getCongruences()) {
        PTRef x = ptRefPair.first;
        PTRef y = ptRefPair.second;
        explainer->explain(enode_store.getERef(x), enode_store.getERef(y));
    }
#endif
    explanation.push(reason_inequality);
    has_explanation = true;
}

void Egraph::explainConstants(ERef p, ERef q) {
    ERef enr_proot = getEnode(p).getRoot();
    ERef enr_qroot = getEnode(q).getRoot();
    assert(logic.isConstant(getEnode(enr_proot).getTerm()));
    assert(logic.isConstant(getEnode(enr_qroot).getTerm()));
    assert(enr_proot != enr_qroot);
    explanation = explainer->explain(enr_proot,enr_qroot);
    has_explanation = true;
}

uint32_t UseVector::addParent(ERef parent) {
    auto index = getFreeSlotIndex();
    auto entry = erefToEntry(parent);
    data[index] = entry;
    ++nelems;
    assert(entryToERef(entry) == parent);
    return index;
}

void UseVector::clearEntryAt(int index) {
    assert(index >= 0 && static_cast<std::size_t>(index) < data.size() && data[index].isValid());
    data[index] = UseVector::indexToFreeEntry(free);
    free = index;
    --nelems;
}

uint32_t UseVector::getFreeSlotIndex() {
    auto ret = free;
    if (ret != Entry::FREE_ENTRY_LIST_GUARD) {
        Entry e = data[free];
        assert(e.isFree());
        free = freeEntryToIndex(e);
        assert(free == Entry::FREE_ENTRY_LIST_GUARD || static_cast<std::size_t>(free) < data.size());
        return ret;
    }
    ret = data.size();
    data.emplace_back();
    return ret;
}

void Egraph::updateUseVectors(PTRef term) {
    ERef eref = termToERef(term);
    auto cid = getEnode(eref).getCid();
    while (cid >= parents.size()) {
        parents.emplace_back();
    }
    addToUseVectors(eref);
}

/**
 * Determines whether some earlier child of the parent enode is in the same congruence class as the given child.
 * @param parent parent enode
 * @param childIndex index in the list of children of child under consideration
 */
bool Egraph::childDuplicatesClass(ERef parent, uint32_t childIndex) {
    assert(childIndex < getEnode(parent).getSize());
    if (childIndex == 0) { return false; }
    Enode const & parentNode = getEnode(parent);
    ERef child = parentNode[childIndex];
    auto childClass = getEnode(getEnode(child).getRoot()).getCid();
    auto precedingChildren = opensmt::span(parentNode.begin(), childIndex);
    return std::any_of(precedingChildren.begin(), precedingChildren.end(), [&](ERef precChild) {
       return childClass == getEnode(getEnode(precChild).getRoot()).getCid();
    });
}

/**
 * Adds the parent enode to the use-vectors of its children.
 *
 * The parent enode remembers its indices in the use-vectors.
 * If two children are in the same congruence class, only the use-vector of the first one remembers the parent.
 */
void Egraph::addToUseVectors(ERef parentRef) {
    Enode & parent = getEnode(parentRef);
    for (uint32_t i = 0; i < parent.getSize(); ++i) {
        ERef childRef = parent[i];
        auto childCid = getEnode(getEnode(childRef).getRoot()).getCid();
        assert(parents.size() > childCid);
        if (childDuplicatesClass(parentRef, i)) {
            parent.setIndex(i, UseVectorIndex::NotValidIndex);
        } else {
            auto index = parents[childCid].addParent(parentRef);
            parent.setIndex(i, UseVectorIndex{index});
        }
    }
}

/**
 * Removes the parent enode from the use-vectors of its children.
 *
 * Note that the indices in the parent are not reset, they remain invalid.
 *
 */
void Egraph::removeFromUseVectors(ERef parent) {
    Enode const & parentNode = getEnode(parent);
    for (uint32_t i = 0; i < parentNode.getSize(); ++i) {
        ERef childRef = parentNode[i];
        auto childCid = getEnode(getEnode(childRef).getRoot()).getCid();
        auto parentIndex = parentNode.getIndex(i);
        if (parentIndex != UseVectorIndex::NotValidIndex) {
            assert(UseVector::entryToERef(parents[childCid][parentIndex.x]) == parent);
            parents[childCid].clearEntryAt(parentIndex.x);
        }
    }
}

/**
 * Removes the parent enode from the use-vectors of its children except the one with the given congruence id.
 *
 * Same as removeFromUseVectors except we keep the parent entry in the use-vector with the given congrunce id.
 */
void Egraph::removeFromUseVectorsExcept(ERef parent, CgId cgid) {
    Enode const & parentNode = getEnode(parent);
    for (uint32_t i = 0; i < parentNode.getSize(); ++i) {
        ERef childRef = parentNode[i];
        auto childCid = getEnode(getEnode(childRef).getRoot()).getCid();
        if (childCid != cgid) {
            auto parentIndex = parentNode.getIndex(i);
            if (parentIndex != UseVectorIndex::NotValidIndex) {
                assert(UseVector::entryToERef(parents[childCid][parentIndex.x]) == parent);
                parents[childCid].clearEntryAt(parentIndex.x);
            }
        }
    }
}
