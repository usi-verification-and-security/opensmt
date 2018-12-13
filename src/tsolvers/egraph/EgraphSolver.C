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

#include "Egraph.h"
#include "Enode.h"
//#include "LA.h"
// DO NOT REMOVE THIS COMMENT !!
// IT IS USED BY CREATE_THEORY.SH SCRIPT !!
// NEW_THEORY_HEADER
//#include "EmptySolver.h"
//#include "BVSolver.h"
//#include "LRASolver.h"
//#include "DLSolver.h"
//#include "CostSolver.h"
//#include "AXDiffSolver.h"
// Added to support compiling templates
//#include "DLSolver.C"
//#include "SimpSMTSolver.h"
#include "TreeOps.h"
#include "Deductions.h"

#define VERBOSE 0

static SolverDescr descr_uf_solver("UF Solver", "Solver for Quantifier Free Theory of Uninterpreted Functions with Equalities");

const char* Egraph::s_val_prefix = "u";
const char* Egraph::s_const_prefix = "n";
const char* Egraph::s_any_prefix = "a";
const char* Egraph::s_val_true = "true";
const char* Egraph::s_val_false = "false";

Egraph::Egraph(SMTConfig & c, Logic& l , vec<DedElem>& d)
      : TSolver            (descr_uf_solver, descr_uf_solver, c, d)
      , logic              (l)
#if defined(PEDANTIC_DEBUG)
      , enode_store        ( logic, forbid_allocator )
#else
      , enode_store        ( logic )
#endif
      , ERef_Nil           ( enode_store.get_Nil() )
      , fa_garbage_frac    ( 0.5 )
      , active_dup1        ( false )
      , active_dup2        ( false )
      , dup_count1         ( 0 )
      , dup_count2         ( 0 )
      , active_dup_map1    ( false )
      , active_dup_map2    ( false )
      , dup_map_count1     ( 0 )
      , dup_map_count2     ( 0 )
      , congruence_running ( false )
      , time_stamp         ( 0 )
#ifdef PRODUCE_PROOF
      , cgraph_            ( new CGraph( *this, config, logic ) )
      , cgraph(NULL)
      , automatic_coloring ( false )
#endif
{
    // For the uninterpreted predicates to work we need to have
    // two special terms true and false, and an asserted disequality
    // true != false

    // This is for the enode store
    // XXX These guys should be defined through the same interface every
    // other term is defined.  This is probably declareTerm()
    ERef ers_true  = enode_store.addSymb(logic.getSym_true());
    ERef ers_false = enode_store.addSymb(logic.getSym_false());
    PTRef ptr_new_true  = enode_store.addTerm(ers_true, ERef_Nil,
                            logic.getTerm_true());
    PTRef ptr_new_false = enode_store.addTerm(ers_false, ERef_Nil,
                            logic.getTerm_false());

    assert(ptr_new_true  == logic.getTerm_true());
    assert(ptr_new_false == logic.getTerm_false());

    PTRef t = logic.getTerm_true();
    PTRef f = logic.getTerm_false();
    enode_store[t].setConstant(t);
    enode_store[f].setConstant(f);

    enode_store.ERef_True  = enode_store.termToERef[t];
    enode_store.ERef_False = enode_store.termToERef[f];
    // add the term (= true false) to term store
    vec<PTRef> tmp;
    tmp.push(logic.getTerm_true());
    tmp.push(logic.getTerm_false());
    PTRef neq = logic.mkEq(tmp);
//    const char* msg;
//    PTRef neq = logic.insertTerm(logic.getSym_eq(), tmp, &msg);
    assert(neq != PTRef_Undef);
    assertNEq(logic.getTerm_true(), logic.getTerm_false(), PtAsgn(neq, l_False));
    Eq_FALSE = neq;
}

//
// Pushes a backtrack point
//
void Egraph::pushBacktrackPoint( )
{
#ifdef VERBOSE_EUF
  cerr << "bt point " << backtrack_points.size() << endl;
#endif
  // Save solver state if required
  backtrack_points.push( undo_stack_main.size( ) );

  // Push ordinary theories <- now done in THandler
//  for ( uint32_t i = 1 ; i < tsolvers.size_( ) ; i ++ )
//    tsolvers[ i ]->pushBacktrackPoint( );

  TSolver::pushBacktrackPoint();
//  deductions_lim .push( th_deductions.size( ) );
//  deductions_last.push( deductions_next );
//  assert( deductions_last.size( ) == deductions_lim.size( ) );
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
// Returns a deduction
//
PtAsgn_reason Egraph::getDeduction( ) {

#ifdef VERBOSE_EUF
    cerr << "deductions available: " << th_deductions.size() - deductions_next << endl;
#endif
    // Communicate UF deductions
    while ( deductions_next < th_deductions.size_( ) ) {
        PtAsgn_reason pta = th_deductions[deductions_next++];
        ERef e             = enode_store.termToERef[pta.tr];
        Enode& en_e        = enode_store[e];
        // For sure this has a deduced polarity
        assert( logic.getPterm(pta.tr).getVar() == -1 || deduced[logic.getPterm(pta.tr).getVar()] != l_Undef );
        // If it has been pushed it is not a good candidate
        // for deduction
        if ( hasPolarity(pta.tr) )
            continue;

#ifdef STATISTICS
        tsolver_stats.deductions_sent ++;
#ifdef VERBOSE_EUF
        cerr << "sent a deduction" << endl;
#endif
//    const int index = e->getDedIndex( );
//    tsolvers_stats[ index ]->deductions_sent ++;
#endif

        return pta;
    }

    // We have already returned all the possible deductions
    return PtAsgn_reason_Undef;
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
    ERef e = enode_store.termToERef[tr];
    suggestions.pop();
    Enode& en_e = enode_store[e];
    if ( hasPolarity(tr) )
      continue;
    if ( logic.getPterm(tr).getVar() == -1 || deduced[logic.getPterm(tr).getVar()] != l_Undef )
      continue;

    return tr;
  }

  // We have already returned all
  // the possible suggestions
  return PTRef_Undef;
}

//
// Communicate conflict
//
void Egraph::getConflict( bool deduction, vec<PtAsgn>& cnfl )
{
    (void)deduction;
    for (int i = 0; i < explanation.size(); i++)
        cnfl.push(explanation[i]);
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
    values.clear();
    values_ok = false;
}

void Egraph::computeModel( )
{
    if (values_ok == true)
        return;

    const vec<ERef>& enodes = enode_store.getEnodes();
    for (int i = 0; i < enodes.size(); i++) {
        if (values.has(enodes[i]))
            continue;
        ERef root_r = enode_store[enodes[i]].getRoot();
        values.insert(enodes[i], root_r);
    }
    values_ok = true;
}

void Egraph::declareAtom(PTRef atom) {
    if (!isValid(atom)) { return; }
    if (isInformed(atom)) { return; }
    declareTermRecursively(atom);
    setInformed(atom);
}

void Egraph::declareTermRecursively(PTRef tr) {
    if (declared.find(tr) != declared.end()) { return; } // already declared
    const Pterm& term = logic.getPterm(tr);
    // declare first the childen and then the current term
    for (int i = 0; i < term.size(); ++i) {
        declareTermRecursively(term[i]);
    }
    declareTerm(tr);
    declared.insert(tr);
}

//
// No recursion here, we assume the caller has already introduced the
// subterms
//
void Egraph::declareTerm(PTRef tr) {

    if (!isValid(tr) && !logic.isUFTerm(tr) && !logic.isBoolAtom(tr)) { return; }

    if (!enode_store.termToERef.has(tr)) {
        const Pterm& tm = logic.getPterm(tr);
        ERef sym = enode_store.addSymb(tm.symb());
        ERef cdr = ERef_Nil;
        for (int j = tm.size()-1; j >= 0; j--) {
            assert(enode_store.termToERef.has(tm[j])); // The child was not inserted
            ERef car = enode_store.termToERef[tm[j]];
#ifdef VERBOSE_EUF
            ERef prev_cdr = cdr;
            assert (enode_store[car].getRoot() == car);
            assert (enode_store[cdr].getRoot() == cdr);
#endif
            cdr = enode_store.addList(car, cdr);
        }
        // Canonize the term representation
#ifdef VERBOSE_EUF
        cerr << "EgraphSolver: Adding term " << logic.printTerm(tr) << " (" << tr.x << ")" << endl;
#endif
        PTRef rval = enode_store.addTerm(sym, cdr, tr);
        assert(rval == tr);
        if (logic.isConstant(rval)) enode_store[rval].setConstant(rval);
    }

    // Check if termToERef contained the ref and it has been rewritten
    // to another term.  This is a bit messy, but will do for now...
    PTRef out = enode_store[enode_store.termToERef[tr]].getTerm();
    if (out != tr) {
        printf("Term changed while being added\n");
        assert(false);
        exit(1);
    }
    if (logic.isDisequality(tr) && !enode_store.dist_classes.has(tr))
        enode_store.addDistClass(tr);

    if (logic.hasSortBool(tr)) {
        Pterm& t = logic.getPterm(tr);
        while (known_preds.size() <= Idx(t.getId()))
            known_preds.push(false);
        known_preds[Idx(t.getId())] = true;
    }
}

lbool Egraph::addEquality(PtAsgn pa) {
    Pterm& pt = logic.getPterm(pa.tr);
    assert(pt.size() == 2);

    if (pt.getVar() != -1 && deduced[pt.getVar()] != l_Undef && deduced[pt.getVar()] == pa.sgn) {
#ifdef VERBOSE_EUF
        cerr << "Assertion already deduced: " << logic.printTerm(pa.tr) << endl;
#endif
        return l_Undef;
    }
    bool res = true;
    PTRef e = pt[0];
    for (int i = 1; i < pt.size() && res == true; i++)
        res = assertEq(e, pt[i], pa);

    if (res) {
#ifdef VERBOSE_EUF
//        cerr << "Asserting the equality to true / false" << endl;
#endif
        bool res2;
        // First: I'm not sure this is the right way to do this!
        // second:
        //  pa.sgn == true if this is an equality literal and false if this
        //  is a distinct
        if (pa.sgn == l_True)
            res2 = addTrue(pa.tr);
        else
            res2 = addFalse(pa.tr);

        assert(res2 != false);
    }

#ifdef STATISTICS
    if (res == false)
        tsolver_stats.unsat_calls++;
    // The sat_calls is increased already in addTrue
#endif

    return res == false ? l_False : l_Undef;
}

lbool Egraph::addDisequality(PtAsgn pa) {
    const Pterm& pt = logic.getPterm(pa.tr);
    bool res = true;

    if (pt.getVar() != -1 && deduced[pt.getVar()] != l_Undef && deduced[pt.getVar()] == pa.sgn) {
#ifdef VERBOSE_EUF
        cerr << "Assertion already deduced: " << logic.printTerm(pa.tr) << endl;
#endif
        return l_Undef;
    }

    if (pt.size() == 2)
        res = assertNEq(pt[0], pt[1], pa);
    else
        res = assertDist(pa.tr, pa);

#ifdef ENABLE_DIST_BOOL // This should be more efficient but osmt1 does not do it
    if (res == true)
#else
    if (res == true && pt.size() == 2)
#endif
    {
#ifdef VERBOSE_EUF
//        cerr << "Asserting the equality to false/true" << endl;
#endif
        bool res2;
        // pa.sgn == true if this is a disequality
        if (pa.sgn == l_True)
            res2 = addTrue(pa.tr);
        else
            res2 = addFalse(pa.tr);
        assert(res2 != false);
    }
#ifdef STATISTICS
    if (!res)
        tsolver_stats.unsat_calls++;
    // The sat_calls is increased already in addFalse
#endif

    return res == false ? l_False : l_Undef;
}

bool Egraph::addTrue(PTRef term) {
    if (logic.getPterm(term).getVar() != -1 && deduced[logic.getPterm(term).getVar()] != l_Undef && deduced[logic.getPterm(term).getVar()] == l_True) {
#ifdef VERBOSE_EUF
        cerr << "Assertion already deduced: " << logic.printTerm(term) << endl;
#endif
        return true;
    }
    bool res = assertEq(term, logic.getTerm_true(), PtAsgn(term, l_True));
#ifdef STATISTICS
    if (res == false)
        tsolver_stats.unsat_calls++;
    else {
        tsolver_stats.sat_calls++;
#ifdef VERBOSE_EUF
        cerr << "sat call" << endl;
#endif
    }
#endif
    return res;
}

bool Egraph::addFalse(PTRef term) {
    if (logic.getPterm(term).getVar() != -1 && deduced[logic.getPterm(term).getVar()] != l_Undef && deduced[logic.getPterm(term).getVar()] == l_False) {
#ifdef VERBOSE_EUF
        cerr << "Assertion already deduced: " << logic.printTerm(term) << endl;
#endif
        return true;
    }
    bool res = assertEq(term, logic.getTerm_false(), PtAsgn(term, l_False));
#ifdef STATISTICS
    if (res == false)
        tsolver_stats.unsat_calls++;
    else {
        tsolver_stats.sat_calls++;
#ifdef VERBOSE_EUF
        cerr << "sat call" << endl;
#endif
    }
#endif
    return res;
}

//===========================================================================
// Private Routines for Core Theory Solver

//
// Assert an equality between nodes x and y
//
bool Egraph::assertEq ( PTRef tr_x, PTRef tr_y, PtAsgn r )
{
    ERef x = termToERef(tr_x);
    ERef y = termToERef(tr_y);
    assert( getEnode(x).isTerm() );
    assert( getEnode(y).isTerm() );
    assert( pending.size() == 0 );
    pending.push( x );
    pending.push( y );

#ifdef VERBOSE_EUF
    cerr << "this is assertEq for " << toString(x)
         << " (enode-id " << tr_x.x << ") and "
         << toString(y) << " (enode-id " << tr_y.x << ")" << endl;

    ELRef elr_x = getEnode(x).getForbid();
    ERef first_x = ERef_Undef;
    if (elr_x == ELRef_Undef)
        cerr << "asserting eq, x's forbid list is undef" << endl;
    else {
        cerr << "asserting eq, x's forbid list is " << endl;
        cerr << printDistinctionList(elr_x, forbid_allocator, false);
    }
    ELRef elr_y = getEnode(y).getForbid();
    ERef first_y = ERef_Undef;
    if (elr_y == ELRef_Undef)
        cerr << "asserting eq, y's forbid list is undef" << endl;
    else {
        cerr << "asserting eq, y's forbid list is " << endl;
        cerr << printDistinctionList(elr_y, forbid_allocator, false);
    }
#endif

    return mergeLoop( r );
}

//
// Merge what is in pending and propagate to parents
//
bool Egraph::mergeLoop( PtAsgn reason )
{
    bool congruence_pending = false;

    while ( pending.size() != 0 ) {
        // Remove a pending equivalence
        assert( pending.size( ) >= 2 );
        assert( pending.size( ) % 2 == 0 );
        ERef p = pending.last( ); pending.pop( );
        ERef q = pending.last( ); pending.pop( );
        const Enode& en_p = getEnode(p);
        const Enode& en_q = getEnode(q);

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

        if ( en_p.isTerm( ) ) {
            expStoreExplanation( p, q, congruence_pending ? PtAsgn(PTRef_Undef, l_Undef) : reason );
#ifdef VERBOSE_EUF
            cerr << "Exp store: " << (congruence_pending ? "undef" : logic.printTerm(reason.tr)) << endl;
#endif
        }

        // Check if they can't be merged
        PtAsgn reason_inequality(PTRef_Undef, l_Undef);
        bool res = unmergeable( en_p.getRoot(), en_q.getRoot(), reason_inequality );

        // They are not unmergable, so they can be merged
        if ( !res ) {
            merge( en_p.getRoot( ), en_q.getRoot( ), reason );
            congruence_pending = true;
            continue;
        }
#ifdef VERBOSE_EUF
        cerr << "Unmergeable: " << logic.printTerm(en_p.getTerm()) << " [" << logic.printTerm(enode_store[en_p.getRoot()].getTerm()) << "] "
                                << logic.printTerm(en_q.getTerm()) << " [" << logic.printTerm(enode_store[en_q.getRoot()].getTerm()) << "]" << endl;
        if (reason_inequality.tr != PTRef_Undef)
            cerr << "Due to " << logic.printTerm(reason_inequality.tr) << endl;
        else
            cerr << "Due to different constants" << endl;
#endif
        has_explanation = true;
        // Conflict detected. We should retrieve the explanation
        // We have to distinguish 2 cases. If the reason for the
        // conflict is ERef_Undef, it means that a conflict arises because
        // we tried to merge two classes that are assigned to different
        // constants, otherwise we have a proper reason
        ERef reason_1 = ERef_Undef;
        ERef reason_2 = ERef_Undef;
        //
        // Different constants
        //
        ERef enr_proot = en_p.getRoot();
        ERef enr_qroot = en_q.getRoot();

        if ( reason_inequality.tr == PTRef_Undef ) {
            const Enode& en_proot = getEnode(enr_proot);
            const Enode& en_qroot = getEnode(enr_qroot);
            assert(en_proot.getConstant() != PTRef_Undef);
            assert(en_qroot.getConstant() != PTRef_Undef);
            assert(enr_proot != enr_qroot);
#ifdef PRODUCE_PROOF
            if ( config.produce_inter() > 0 ) {
                cgraph_->setConf( en_proot.getConstant( )
                        , en_qroot.getConstant( )
                        , PTRef_Undef );
            }
#endif
            //
            // We need explaining
            //
            // 1. why p and p->constant are equal
#ifdef VERBOSE_EUF
            cerr << "constant pushing (1): "
                 << logic.printTerm(en_p.getTerm()) << " and "
                 << logic.printTerm(en_proot.getConstant()) << endl;
#endif
            exp_pending.push( p );
            exp_pending.push( enr_proot );
            // 2. why q and q->constant are equal
#ifdef VERBOSE_EUF
            cerr << "constant pushing (2): "
                 << logic.printTerm(en_q.getTerm()) << " and "
                 << logic.printTerm(en_qroot.getConstant()) << endl;
#endif
            exp_pending.push( q );
            exp_pending.push( enr_qroot );
            // 3. why p and q are equal
#ifdef VERBOSE_EUF
            cerr << "constant pushing (3): "
                 << logic.printTerm(en_q.getTerm()) << " and "
                 << logic.printTerm(en_p.getTerm()) << endl;
#endif
            exp_pending.push( q );
            exp_pending.push( p );
#ifdef VERBOSE_EUF
            cerr << "Explain XXX" << endl;
#endif
            initDup1( );
            expExplain( );
 #ifdef PRODUCE_PROOF
            if ( config.produce_inter() > 0 ) {
                delete cgraph;
                cgraph = cgraph_;
                //cgraphs.push(cgraph_);
                cgraph_ = new CGraph(*this, config, logic);
            }
#endif
           doneDup1( );
            expCleanup(); // Should be organized better...
        }
        // Does the reason term correspond to disequality symbol
        else if ( logic.isDisequality(logic.getPterm(reason_inequality.tr).symb()) ) {
            // The reason is a distinction, but skip the false equality
            if (reason_inequality.tr != Eq_FALSE)
                explanation.push( reason_inequality );
            // We should iterate through the elements
            // of the distinction and find which atoms
            // are causing the conflict
            const Pterm& pt_reason = logic.getPterm(reason_inequality.tr);
            for (int i = 0; i < pt_reason.size(); i++) {
                // (1) Get the proper term reference from pos i in the distinction
                // (2) Get the enode corresponding to the proper term
                // (3) Find the enode corresponding to the root
                // (4) Check if the root enode is the same as the root of p or q

                PTRef ptr_arg = pt_reason[i];                             // (1)
                ERef  enr_arg = enode_store.termToERef[ptr_arg];          // (2)
                ERef  enr_arg_root = enode_store[enr_arg].getRoot();      // (3)

                // (4)
                if ( enr_arg_root == enr_proot ) { assert( reason_1 == ERef_Undef ); reason_1 = enr_arg; }
                if ( enr_arg_root == enr_qroot ) { assert( reason_2 == ERef_Undef ); reason_2 = enr_arg; }
            }
            assert( reason_1 != ERef_Undef );
            assert( reason_2 != ERef_Undef );
#ifdef VERBOSE_EUF
            cerr << "Explain YYY" << endl;
#endif
#ifdef PRODUCE_PROOF
            expExplain( reason_1, reason_2, reason_inequality.tr );
#else
            expExplain( reason_1, reason_2 );
#endif
        }
        else if ( logic.isEquality(logic.getPterm(reason_inequality.tr).symb()) ) {
            // The reason is a negated equality
            assert(reason_inequality.sgn == l_False);
#ifdef VERBOSE_EUF
            cerr << "Reason inequality " << logic.printTerm(reason_inequality.tr) << endl;
#endif
            const Pterm& pt_reason = logic.getPterm(reason_inequality.tr);

            if (reason_inequality.tr != Eq_FALSE)
                explanation.push(reason_inequality);

            // The equality
            // If properly booleanized, the left and righ sides of equality
            // will always be UF terms
            // The left hand side of the equality
            reason_1 = enode_store.termToERef[pt_reason[0]];
            // The rhs of the equality
            reason_2 = enode_store.termToERef[pt_reason[1]];

            assert( reason_1 != ERef_Undef );
            assert( reason_2 != ERef_Undef );

#ifdef VERBOSE_EUF
            cerr << "Explain ZZZ " << toString(reason_1) << " " << toString(reason_2) << " " << logic.printTerm(reason_inequality.tr) << endl;
#endif
#ifdef PRODUCE_PROOF
            expExplain( reason_1, reason_2, reason_inequality.tr );
#else
            expExplain( reason_1, reason_2 );
#endif
        }
        else if ( logic.isUP(reason_inequality.tr) ) {
            // The reason is an uninterpreted predicate
            assert(false);
            if (reason_inequality.tr != Eq_FALSE)
                explanation.push(reason_inequality);
        }
        // Clear remaining pendings
        pending.clear( );
        // Remove the last explanation that links
        // the two unmergable classes
        expRemoveExplanation( );
//        expCleanup(); // called in expExplain(r1, r2)
        // Return conflict
        return false;
    }
    return true;
}

//
// Assert a disequality between nodes x and y
//
bool Egraph::assertNEq ( PTRef x, PTRef y, PtAsgn r )
{
#ifdef VERBOSE_EUF
    cerr << "Assert NEQ of " << logic.printTerm(x) << " and " << logic.printTerm(y) << " since " << logic.printTerm(r.tr) << endl;
#endif
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
    ERef xe = enode_store.termToERef[x];
    ERef ye = enode_store.termToERef[y];
    ERef p = getEnode(xe).getRoot();
    ERef q = getEnode(ye).getRoot();

    // They can't be different if the nodes are in the same class
    if ( p == q ) {
        if (r.tr != Eq_FALSE) explanation.push( r );
#ifdef VERBOSE_EUF
        cerr << "Explain XXY" << endl;
#endif
#ifdef PRODUCE_PROOF
        expExplain( xe, ye, r.tr );
#else
        expExplain( xe, ye );
#endif
        has_explanation = true;
        return false;
    }

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
#ifdef VERBOSE_EUF
    cerr << "Reason is " << logic.printTerm(r.tr) << endl;
#endif
    ELRef pdist = ELRef_Undef;
    Enode& en_q = enode_store[q];
    if ( en_q.getForbid() == ELRef_Undef ) {
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
    Enode& en_p = enode_store[p];
    if ( en_p.getForbid() == ELRef_Undef ) {
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
#ifdef VERBOSE_EUF
    cerr << printDistinctionList(en_q.getForbid(), forbid_allocator, false);
//    undo_stack_main.last().bool_term = r.tr;
#endif


    return true;
}

// Assert a distinction on arguments of tr_d

bool Egraph::assertDist( PTRef tr_d, PtAsgn tr_r )
{
    assert(tr_d == tr_r.tr);

    // Retrieve distinction number
    int index = enode_store.getDistIndex(tr_d);
    // While asserting, check that no two nodes are congruent
    Map< enodeid_t, ERef, EnodeIdHash, Equal<enodeid_t> > root_to_enode;
    // Nodes changed
    vec<ERef> nodes_changed;
    // Assign distinction flag to all arguments
    const Pterm& pt_d = logic.getPterm(tr_d);
#ifdef VERBOSE_EUF
    cerr << "Distinction check for " << logic.printTerm(tr_d) << endl;
#endif
    for (int i = 0; i < pt_d.size(); i++) {
        PTRef tr_c = pt_d[i];
        ERef er_c = enode_store.termToERef[tr_c];
        Enode& en_c = enode_store[er_c];
        assert(en_c.isTerm());
        enodeid_t root_id = enode_store[en_c.getRoot()].getId();
#ifdef VERBOSE_EUF
        cerr << "  Checking distinction member " << logic.printTerm(tr_c) << " with root " << logic.printTerm(enode_store.ERefToTerm[en_c.getRoot()]) << " (" << root_id << ")" << endl;
#endif
        if ( root_to_enode.has(root_id) ) {
            // Two equivalent nodes in the same distinction. Conflict
            if (tr_r.tr != Eq_FALSE) {
                explanation.push(tr_r);
                has_explanation = true;
            }
            // Extract the other node with the same root
            ERef p = root_to_enode[root_id];
#ifdef VERBOSE_EUF
            cerr << "  Distinction members " << logic.printTerm(tr_c) << " and " << logic.printTerm(enode_store.ERefToTerm[p]) << " are equal" << endl;
#endif
            // Check condition
            assert( enode_store[p].getRoot() == en_c.getRoot() );
            // Retrieve explanation
#ifdef VERBOSE_EUF
            cerr << "Explain XYX" << endl;
#endif
#ifdef PRODUCE_PROOF
            expExplain( er_c, p, tr_r.tr );
#else
            expExplain( er_c, p);
#endif
            // Revert changes, as the current context is inconsistent
            while( nodes_changed.size() != 0 ) {
                ERef n = nodes_changed.last();
                nodes_changed.pop();
                // Deactivate distinction in n
                Enode& en_n = enode_store[n];
                en_n.setDistClasses( en_n.getDistClasses() & ~(SETBIT( index )) );
            }
            return false;
        }
        else
            root_to_enode.insert(root_id, er_c);
        // Activate distinction in e
        en_c.setDistClasses(en_c.getDistClasses() | SETBIT(index));
        nodes_changed.push(er_c);
#ifdef VERBOSE_EUF
        cerr << "  Activating distinction of " << logic.printTerm(tr_c) << endl;
#endif
    }
    // Distinction pushed without conflict
    undo_stack_main.push(Undo(DIST, tr_d));
    return true;
}

void Egraph::undoDistinction(PTRef tr_d) {
#ifdef VERBOSE_EUF
    cerr << "Undo distinction: " << logic.printTerm(tr_d) << endl;
#endif
    dist_t index = enode_store.getDistIndex(tr_d);
    Pterm& pt_d = logic.getPterm(tr_d);
    for (int i = 0; i < pt_d.size(); i++) {
        PTRef tr_c = pt_d[i];
        ERef er_c = enode_store.termToERef[tr_c];
        Enode& en_c = enode_store[er_c];
        assert(en_c.isTerm());
        en_c.setDistClasses( en_c.getDistClasses() & ~(SETBIT(index)) );
    }
}

//
// Backtracks stack to a certain size
//
void Egraph::backtrackToStackSize ( size_t size ) {
#ifdef VERBOSE_EUF
    printf("Backtracking to size %d\n", (int)size);
#endif
    // Make sure explanation is cleared
    // (might be empty, though, if boolean backtracking happens)
    explanation.clear();
    has_explanation = false;

    //
    // Restore state at previous backtrack point
    //
//    printf("stack size %d > %d\n", undo_stack_term.size(), size);
    while ( undo_stack_main.size_() > size ) {
        Undo u = undo_stack_main.last();
        oper_t last_action = u.oper;

        undo_stack_main.pop();

        if ( last_action == MERGE ) {
            ERef e = u.arg.er;
            Enode& en_e = enode_store[e];
#ifdef VERBOSE_EUF
//            if (en_e.type() == Enode::et_list)
//                cerr << "Undo merge of list" << endl;
//            else
//                cerr << "Undo merge: " << logic.printTerm(en_e.getTerm()) << endl;
//            if (en_e.type() != Enode::et_list)
//                cerr << "Undo merge: " << logic.printTerm(en_e.getTerm()) << endl;
#endif
            undoMerge( e );
            if ( en_e.isTerm( ) ) {
                expRemoveExplanation( );
            }
        }

#if MORE_DEDUCTIONS
        else if ( last_action == ASSERT_NEQ ) {
            ERef e = u.arg.er;
            assert( neq_list.last( ) == e );
            neq_list.pop( );
        }
#endif

        else if ( last_action == DISEQ ) {
            ERef e = u.arg.er;
            Enode& en_e = enode_store[e];
            undoDisequality( e );
        }
        else if ( last_action == DIST ) {
            PTRef ptr = u.arg.ptr;
            undoDistinction( ptr );
        }
        else if ( last_action == CONS )
//      undoCons( e );
        ;
        else if ( last_action == SET_POLARITY) {
            assert(hasPolarity(u.arg.ptr));
            clearPolarity(u.arg.ptr);
        } else
            opensmt_error( "unknown action" );
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
#ifdef VERBOSE_EUF
//    cerr << "Asserting equality of the following enodes: " << endl
//         << enode_store.printEnode(x) << endl
//         << enode_store.printEnode(y) << endl;
    if (enode_store[x].isTerm())
        cerr << "Asserting equality of " << logic.printTerm(enode_store[x].getTerm()) << " and "
             << logic.printTerm(enode_store[y].getTerm()) << endl;
    cerr << "x size is " << enode_store[x].getSize() << endl;
    cerr << "x isTerm is " << enode_store[x].isTerm() << endl;
    cerr << "x isConstant is " << isConstant(x) << endl;
    cerr << "y size is " << enode_store[y].getSize() << endl;
    cerr << "y isTerm is " << enode_store[y].isTerm() << endl;
    cerr << "y isConstant is " << isConstant(y) << endl;
#endif
    { // sanity checks
        const Enode& an_x = getEnode(x);
        const Enode& an_y = getEnode(y);

        if (an_x.isTerm()) {
            assert( !isConstant(x) || !isConstant(y) );
//        assert( !isConstant(x) || an_x.getSize() == 1 );
//        assert( !isConstant(y) || an_y.getSize() == 1 );
        }
        assert( an_x.getRoot( ) != an_y.getRoot( ) );
        assert( x == an_x.getRoot( ) );
        assert( y == an_y.getRoot( ) );
    }


    // Ensure that the constant or the one with a larger equivalence
    // class will be in x (and will become the root)
    if (isConstant(y) ||
        (!(isConstant(x)) && (getEnode(x).getSize() < getEnode(y).getSize())))
    {
        std::swap(x,y);
    }
    // Get the references right here
    Enode& en_x = getEnode(x);
    Enode& en_y = getEnode(y);

    assert(en_x.type() == en_y.type());
    assert(!en_y.isTerm() || !isConstant(y));

    // TODO:
    // Propagate equalities to other ordinary theories
    //

    // Update forbid list for x by adding elements of y
    addForbidList(en_x, en_y);
#ifdef GC_DEBUG
    checkRefConsistency();
    checkForbidReferences(x);
#endif
    // Merge distinction classes
    mergeDistinctionClasses(en_x, en_y);
    // Assign w to the class with fewer parents
    ERef w = en_x.getParentSize() < en_y.getParentSize( ) ? x : y ;
//    removeSignatureOfRootedParents(w);

    // Compute deductions that follows from
    // merging x and y. Probably this function
    // could be partially embedded into the next
    // cycle. However, for the sake of simplicity
    // we prefer to separate the two contexts
    if ( config.uf_theory_propagation > 0 ) {
        deduce( x, y, reason );
    }

    mergeCongruenceClassInfo(x, y);

    // Preserve signatures of larger parent set
    if ( en_x.getParentSize() < en_y.getParentSize() )
    {
        enodeid_t tmp = en_x.getCid();
        en_x.setCid( en_y.getCid() );
        en_y.setCid( tmp );
    }
    // Insert new signatures and propagate congruences
    propagateEqualityByCongruence(w);
    // Merge parent lists
    mergeParentLists(en_x, en_y);
    // Store info about the constant
    updateConstantInfo(en_x, en_y);

  // Push undo record
    undo_stack_main.push( Undo(MERGE,y) );
}

//
// Deduce facts from the merge of x and y
//
// FIXME The implementation of polarity deduction should be based on just checking the
//       enode against true/false.  Or possibly the trail should be available for checking.
//       2014-07-01 fixed?
//
void Egraph::deduce( ERef x, ERef y, PtAsgn reason ) {
    if (enode_store[x].isList()) return;
    lbool deduced_polarity = l_Undef;


    PTRef x_const = enode_store[x].getConstant();
    if ( x_const == logic.getTerm_true() )
        deduced_polarity = l_True;
    else if ( x_const == logic.getTerm_false() )
        deduced_polarity = l_False;

    // Let y store the representant of the class
    // containing the facts that we are about to deduce
    if ( deduced_polarity == l_Undef ) {
        ERef tmp = x;
        x = y;
        y = tmp;
        PTRef x_const = enode_store[x].getConstant();
        if ( x_const == logic.getTerm_true() )
            deduced_polarity = l_True;
        else if ( x_const == logic.getTerm_false() )
            deduced_polarity = l_False;
    }

#ifdef VERBOSE_EUF
    lbool deduced_polarity2 = l_Undef;
    if ( x == enode_store.getEnode_true() )
        deduced_polarity2 = l_True;
    else if ( x == enode_store.getEnode_false() )
        deduced_polarity2 = l_False;
    else if (isEqual(enode_store[x].getTerm(), logic.getTerm_true()))
        deduced_polarity2 = l_True;
    else if (isEqual(enode_store[x].getTerm(), logic.getTerm_false()))
        deduced_polarity2 = l_False;

    if ( deduced_polarity2 == l_Undef ) {
        ERef tmp = x;
        x = y;
        y = tmp;
    }

    if ( x == enode_store.getEnode_true() )
        deduced_polarity2 = l_True;
    else if ( x == enode_store.getEnode_false() )
        deduced_polarity2 = l_False;
    else if (isEqual(enode_store[x].getTerm(), logic.getTerm_true()))
        deduced_polarity2 = l_True;
    else if (isEqual(enode_store[x].getTerm(), logic.getTerm_false()))
        deduced_polarity2 = l_False;

    if (deduced_polarity != deduced_polarity2)
        assert(false);
#endif

    if ( deduced_polarity == l_Undef ) { // True, for instance, if x & y are not boolean types, or if they are, but they have not been assigned a value yet
#ifdef VERBOSE_EUF
        assert(enode_store[x].isList() ||
               (!isEqual(enode_store[x].getTerm(), logic.getTerm_true()) &&
                !isEqual(enode_store[x].getTerm(), logic.getTerm_false()) &&
                !isEqual(enode_store[y].getTerm(), logic.getTerm_true()) &&
                !isEqual(enode_store[y].getTerm(), logic.getTerm_false())));
#endif
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
#ifdef VERBOSE_EUF
                    cerr << "Neg-Deducing ";
                    cerr << "not " << logic.printTerm(eq);
                    cerr << " since ";
                    cerr << logic.printTerm(enode_store[x].getTerm());
                    cerr << " and ";
                    cerr << logic.printTerm(enode_store[y].getTerm());
                    cerr << " are now equal";
                    cerr << endl;
#endif
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

    ERef v = y;
    const ERef vstart = v;
    for (;;) {
        // We deduce only things that aren't currently assigned or
        // that we previously deduced on this branch
        ERef sv = v;
        PTRef sv_tr = enode_store[sv].getTerm();
        if (logic.getPterm(sv_tr).getVar() == -1 || deduced[logic.getPterm(sv_tr).getVar()] == l_Undef) {
            if (!hasPolarity(sv_tr) && (logic.getPterm(sv_tr).getVar() == -1 || deduced[logic.getPterm(sv_tr).getVar()] == l_Undef))
            {
                if (logic.getPterm(sv_tr).getVar() != -1) 
                    deduced[logic.getPterm(sv_tr).getVar()] = {id, deduced_polarity};
#ifdef VERBOSE_EUF
                cerr << "Deducing ";
                cerr << (deduced_polarity == l_False ? "not " : "");
                cerr << logic.printTerm(enode_store[sv].getTerm());
                cerr << " since ";
                cerr << logic.printTerm(enode_store[x].getTerm());
                cerr << " and ";
                cerr << logic.printTerm(enode_store[y].getTerm());
                cerr << " are now equal";
                cerr << endl;
#endif
                th_deductions.push(PtAsgn_reason(enode_store.ERefToTerm[sv],
                                              deduced_polarity, reason.tr));
#ifdef STATISTICS
                tsolver_stats.deductions_done ++;
#endif
            }
        }
        v = enode_store[v].getNext( );
        if ( v == vstart )
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
#ifdef VERBOSE_EUF
    cerr << "Undo merge" << endl;
#endif
    assert( y != ERef_Undef );

    Enode& en_y = enode_store[y];

    // x is the node that was merged with y
    ERef x = en_y.getRoot( );

    assert( x != ERef_Undef );

    Enode& en_x = enode_store[x];

    // Undoes the merge of the parent lists
    unmergeParentLists(en_x, en_y);

    // Assign w to the smallest parent class
    ERef w = en_x.getParentSize( ) < en_y.getParentSize( ) ? x : y ;
    assert(w != ERef_Undef);
    Enode& en_w = enode_store[w];
    // Undoes the insertion of the modified signatures
    removeSignatureOfRootedParents(w); // MB: why this?

    undomergeCongruenceClassInfo(x, y);
    // Undo swapping
    if ( en_x.getParentSize( ) < en_y.getParentSize( ) ) {
        enodeid_t tmp = en_x.getCid( );
        en_x.setCid( en_y.getCid( ) );
        en_y.setCid( tmp );
    }
    // Reinsert back signatures that have been removed during
    // the merge operation
    reinsertSignatures(w);
    // Restore distinction classes for x, with a set difference operation
    en_x.setDistClasses( ( en_x.getDistClasses() & ~(en_y.getDistClasses())) );

    undoAddForbidList(en_x, en_y);

    undoUpdateConstantInfo(en_x, en_y);

  //
  // TODO: unmerge for ordinary theories
  //
#ifdef GC_DEBUG
    checkRefConsistency();
#endif
}

//
// Restore the state before the addition of a disequality
//
void Egraph::undoDisequality ( ERef x )
{
#ifdef GC_DEBUG
    checkRefConsistency();
#endif
    Enode& en_x = enode_store[x];
    assert( en_x.getForbid() != ELRef_Undef );

    // We have to distinguish two cases:
    // If there is only one node, that is the
    // distinction to remove
    ELRef xfirst = en_x.getForbid( );
    ERef y = ERef_Undef;
    Elist& el_xfirst = forbid_allocator[xfirst];
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
    Elist& el_yfirst = forbid_allocator[yfirst];
    assert( el_yfirst.link != yfirst || el_yfirst.e == x );
    assert( el_yfirst.link == yfirst || forbid_allocator[el_yfirst.link].e == x );
    assert( en_x.getRoot( ) != en_y.getRoot( ) );

    ELRef ydist = el_xfirst.link == xfirst ? xfirst : el_xfirst.link;
    Elist& el_ydist = forbid_allocator[ydist];

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
    Elist& el_xdist = forbid_allocator[xdist];

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


bool Egraph::unmergeable (ERef x, ERef y, PtAsgn& r)
{
    assert( x != ERef_Undef );
    assert( y != ERef_Undef );

    ERef p = getEnode(x).getRoot();
    ERef q = getEnode(y).getRoot();

#ifdef VERBOSE_EUF
    if (enode_store[x].isTerm()) {
        cerr << "Checking unmergeability of "
             << logic.printTerm(enode_store[x].getTerm())
             << " (" << p.x << ") "
             << " [" << logic.printTerm(enode_store[p].getTerm())
             << "] and "
             << logic.printTerm(enode_store[y].getTerm())
             << " (" << q.x << ") "
             << " [" << logic.printTerm(enode_store[q].getTerm())
             << "]" << endl;
    }
#endif

    // If they are in the same class, they can merge
    if ( p == q ) return false;
    // Check if they have different constants. It is sufficient
    // to check that they both have a constant. It is not
    // possible that the constant is the same. In fact if it was
    // the same, they would be in the same class, but they are not
    // Check if they are part of the same distinction (general distinction)
    const Enode& en_p = getEnode(p);
    const Enode& en_q = getEnode(q);
    if ( en_p.isTerm() && en_p.getConstant() != PTRef_Undef && en_q.getConstant() != PTRef_Undef) return true;
    dist_t intersection = ( en_p.getDistClasses( ) & en_q.getDistClasses( ) );

    if ( intersection ) {
        // Compute the first index in the intersection
        // TODO: Use hacker's delight
        unsigned index = 0;
        while ( ( intersection & 1 ) == 0 ) {
            intersection = intersection >> 1;
            index ++;
        }
        // Dist terms are all inequalities, hence their polarity's true
        r = PtAsgn(enode_store.getDistTerm(index), l_True);
        assert( r.tr != PTRef_Undef );
        return true;
    }
    // Check forbid lists (binary distinction)
    const ELRef pstart = en_p.getForbid( );
    const ELRef qstart = en_q.getForbid( );
    // If at least one is empty, they can merge
    if ( pstart == ELRef_Undef || qstart == ELRef_Undef )
        return false;

    ELRef pptr = pstart;
    ELRef qptr = qstart;

    r = PtAsgn(PTRef_Undef, l_True);

    for (;;) {
        const Elist& el_pptr = forbid_allocator[pptr];
        const Elist& el_qptr = forbid_allocator[qptr];
        // They are unmergeable if they are on the other forbid list
        if ( enode_store[el_pptr.e].getRoot( ) == q ) {
#ifdef VERBOSE_EUF
            cerr << "Unmergeable-q: " << logic.printTerm(enode_store[q].getTerm()) << endl;
            cerr << " - reason: " << logic.printTerm(el_pptr.reason.tr) << endl;
#endif
            r = el_pptr.reason;
            return true;
        }
        if ( enode_store[el_qptr.e].getRoot( ) == p ) {
#ifdef VERBOSE_EUF
            cerr << "Unmergeable-p: " << logic.printTerm(enode_store[p].getTerm()) << endl;
            cerr << " - reason: " << logic.printTerm(el_qptr.reason.tr) << endl;
#endif
            r = el_qptr.reason;
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
    assert( r.tr == PTRef_Undef );
    return false;
}

bool Egraph::assertLit(PtAsgn pta, bool)
{
    // invalidate values
    lbool sgn = pta.sgn;
    PTRef pt_r = pta.tr;
    const Pterm& pt = logic.term_store[pt_r];

    assert(!hasPolarity(pt_r));

    lbool res;
    undo_stack_main.push(Undo(SET_POLARITY, pt_r));

    // Watch out here! the second argument of PtAsgn constructor is
    // in fact lbool!
    if (logic.isEquality(pt.symb()) && sgn == l_True) {
        setPolarity(pt_r, l_True);
        res = addEquality(PtAsgn(pt_r, l_True));
    }
    else if (logic.isEquality(pt.symb()) && sgn == l_False) {
        setPolarity(pt_r, l_False);
        res = addDisequality(PtAsgn(pt_r, l_False));
    }
    else if (logic.isDisequality(pt.symb()) && sgn == l_True) {
        setPolarity(pt_r, l_True);
        res = addDisequality(PtAsgn(pt_r, l_True));
    }
    else if (logic.isDisequality(pt.symb()) && sgn == l_False) {
        setPolarity(pt_r, l_False);
        res = addEquality(PtAsgn(pt_r, l_False));
    }
    else if (logic.isUP(pt_r) && sgn == l_True) {
        setPolarity(pt_r, l_True);
        res = addTrue(pt_r) == false ? l_False : l_Undef;
    }
    else if (logic.isUP(pt_r) && sgn == l_False) {
        setPolarity(pt_r, l_False);
        res = addFalse(pt_r) == false ? l_False : l_Undef;
    }
    else
        assert(false);

    (res == l_False) ? tsolver_stats.unsat_calls ++ : tsolver_stats.sat_calls ++;
    return (res == l_False) ? false : true;
}

//
// Pushes a backtrack point
//
void Egraph::extPushBacktrackPoint( )
{
  // Save solver state if required
  backtrack_points.push( undo_stack_main.size( ) );
}

//
// Pops a backtrack point
//
void Egraph::extPopBacktrackPoint( )
{
  assert( backtrack_points.size( ) > 0 );
  size_t undo_stack_new_size = backtrack_points.last( );
  backtrack_points.pop( );
  backtrackToStackSize( undo_stack_new_size );
}

// The value method

ValPair
Egraph::getValue(PTRef tr)
{
    if (!values_ok) {
        assert(false);
        return ValPair_Undef;
    }
    char* name;

    if (!enode_store.has(tr)) {
        // This variable was never pushed to Egraph so its value is not
        // bound by anything.
        asprintf(&name, "%s%d", s_any_prefix, Idx(logic.getPterm(tr).getId()));
    }
    else {

        Enode& e = enode_store[tr];
        ERef e_root = values[e.getERef()];

        if (e_root == enode_store.ERef_True)
           asprintf(&name, "true");
        else if (e_root == enode_store.ERef_False)
            asprintf(&name, "false");
        else if (isConstant(e_root)) {
            char* const_name = logic.printTerm(enode_store[e_root].getTerm());
            asprintf(&name, "%s%s", s_const_prefix, const_name);
            free(const_name);
        }
        else
            asprintf(&name, "%s%d", s_val_prefix, enode_store[e_root].getId());
    }
    ValPair vp(tr, name);
    free(name);
    return vp;
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
            int id = to[er].getId();
            for (int j = 0; j < to.referenced_by[id].size(); j++) {
#ifdef GC_DEBUG
                cerr << "Updating owner references" << endl;
#endif
                ERef o = to.referenced_by[id][j];
                assert(o != ERef_Undef);
                enode_store[o].setForbid(er);
#ifdef GC_DEBUG
                assert(to[er].getId() == to[enode_store[o].getForbid()].getId());
#endif
            }
            if (prev_fx != ELRef_Undef)
                to[prev_fx].link = er;
            if (done == true) break;
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

void Egraph::addForbidList(Enode & to, const Enode & from) {
    if ( from.getForbid( ) != ELRef_Undef ) {
        // We assign the same forbid list
        if ( to.getForbid( ) == ELRef_Undef ) {
            to.setForbid( from.getForbid( ) );
            forbid_allocator.addReference(to.getForbid(), to.getERef());
        }
            // Otherwise we splice the two lists
        else {
            ELRef tmp = forbid_allocator[to.getForbid()].link;
            forbid_allocator[to.getForbid()].link = forbid_allocator[from.getForbid()].link;
            forbid_allocator[from.getForbid()].link = tmp;
        }
    }
}

void Egraph::mergeDistinctionClasses(Enode & to, const Enode & from) {
    to.setDistClasses( ( to.getDistClasses( ) | from.getDistClasses( ) ) );
}

void Egraph::removeSignatureOfRootedParents(ERef noderef) {
    // Visit each parent of w, according to the type of w
    // and remove each congruence root from the signature table
    const Enode& node = getEnode(noderef);
    ERef p = node.getParent();
    const ERef pstart = p;
    const bool scdr = node.isList( );
    for ( ; p != ERef_Undef ; ) {
        const Enode& en_p = getEnode(p);
        assert ( en_p.isTerm( ) || en_p.isList( ) );
        // If p is a congruence root
        if ( p == en_p.getCgPtr( ) ) {
            assert( enode_store.containsSig( p ));
            enode_store.removeSig(p);
        }
        // Next element
        p = scdr ? en_p.getSameCdr( ) : en_p.getSameCar( ) ;
        // End of cycle
        if ( p == pstart )
            p = ERef_Undef;
    }
}

void Egraph::mergeCongruenceClassInfo(ERef newroot, ERef oldroot) {
    // Perform the union of the two equivalence classes
    // i.e. reroot every node in y's class to point to x
    ERef v = oldroot;
    const ERef vstart = v;
#ifdef VERBOSE_EUF
    bool constant_shouldset = false;
    bool constant_set = false;
#endif
    while (true) {
        Enode& en_v = getEnode(v);
#ifdef VERBOSE_EUF
        if (isConstant(v)) {
            cerr << "Rerooting " << logic.printTerm(en_v.getTerm()) << endl;
            constant_shouldset = true;
        }
#endif
        en_v.setRoot(newroot);
        v = en_v.getNext();
        if (v == vstart)
            break;
    }

    // Splice next lists
    Enode& en_x = getEnode(newroot);
    Enode& en_y = getEnode(oldroot);
    ERef tmp = en_x.getNext();
    en_x.setNext( en_y.getNext() );
    en_y.setNext( tmp );
    // Update size of the congruence class
    en_x.setSize( en_x.getSize( ) + en_y.getSize( ) );
}

void Egraph::propagateEqualityByCongruence(ERef node) {
    ERef p = getEnode(node).getParent();
    const bool scdr = getEnode(node).isList( );
    const ERef pstart = p;
    for ( ; p != ERef_Undef; ) {
        Enode& en_p = getEnode(p);
        // If p is a congruence root
        if ( p == en_p.getCgPtr( ) ) {
            //ERef q = EnodeStore.insertSig(p);
            // Signature already present
            //if ( q != p )
            if (enode_store.containsSig(p)) {
                ERef q = enode_store.lookupSig(p);
                en_p.setCgPtr( q );
                pending.push( p );
                pending.push( q );
            }
            else enode_store.insertSig(p);
        }
        // Next element
        p = scdr ? en_p.getSameCdr( ) : en_p.getSameCar( ) ;
        // Exit if cycle complete
        if ( p == pstart )
            p = ERef_Undef;
    }
}

void Egraph::mergeParentLists(Enode & to, const Enode & from) {
    if ( from.getParent() != ERef_Undef ) {
        // If x has no parents, we assign y's one
        if ( to.getParent() == ERef_Undef ) {
            assert( to.type() == from.type() );
            to.setParent( from.getParent() );
        }
            // Splice the parent lists
        else {
            if ( to.isList() ) {
                ERef tmp = enode_store[to.getParent()].getSameCdr();
                enode_store[to.getParent()].setSameCdr( enode_store[from.getParent()].getSameCdr( ) );
                enode_store[from.getParent()].setSameCdr( tmp );
            }
            else {
                ERef tmp = enode_store[to.getParent()].getSameCar();
                enode_store[to.getParent()].setSameCar( enode_store[from.getParent()].getSameCar() );
                enode_store[from.getParent()].setSameCar( tmp );
            }
        }
    }
    // Adjust parent size
    to.setParentSize( to.getParentSize( ) + from.getParentSize( ) );
}

void Egraph::updateConstantInfo(Enode & to, Enode & from) {
    if (from.isTerm() && from.getConstant() != PTRef_Undef) {
        assert(to.getConstant() == PTRef_Undef);
        to.setConstant( from.getConstant() );
#ifdef VERBOSE_EUF
        constant_set = true;
#endif
    }
        // Store info about the constant
    else if (to.isTerm() && to.getConstant() != PTRef_Undef) {
        assert(from.getConstant() == PTRef_Undef);
        from.setConstant(to.getConstant());
#ifdef VERBOSE_EUF
        constant_set = true;
#endif
    }

#ifdef VERBOSE_EUF
    if (constant_shouldset && !constant_set)
        assert(false);
#endif
}

void Egraph::unmergeParentLists(Enode & to, const Enode & from) {
    to.setParentSize( to.getParentSize() - from.getParentSize() );
    // Restore the correct parents
    if ( from.getParent( ) != ERef_Undef ) {
        // If the parents are equal, that means that
        // y's parent has been assigned to x
        if ( to.getParent( ) == from.getParent( ) )
            to.setParent( ERef_Undef );
            // Unsplice the parent lists
        else {
            assert( to.getParent() != ERef_Undef );
            if ( to.isList( ) ) {
                ERef tmp = enode_store[to.getParent()].getSameCdr();
                enode_store[to.getParent()].setSameCdr( enode_store[from.getParent()].getSameCdr() );
                enode_store[from.getParent()].setSameCdr( tmp );
            }
            else {
                ERef tmp = enode_store[to.getParent()].getSameCar();
                enode_store[to.getParent()].setSameCar( enode_store[from.getParent()].getSameCar() );
                enode_store[from.getParent()].setSameCar( tmp );
            }
        }
    }
}

void Egraph::undomergeCongruenceClassInfo(ERef newroot, ERef oldroot) {
    Enode & en_x = getEnode(newroot);
    Enode & en_y = getEnode(oldroot);
    // Restore the size of x's class
    en_x.setSize( en_x.getSize( ) - en_y.getSize( ) );
    // Unsplice next lists
    ERef tmp = en_x.getNext( );
    en_x.setNext( en_y.getNext( ) );
    en_y.setNext( tmp );
    // Reroot each node of y's eq class back to y
    ERef v = oldroot;
    const ERef vstart = v;
    while (true) {
        Enode& en_v = enode_store[v];
        en_v.setRoot( oldroot );
        v = en_v.getNext( );
        if ( v == vstart )
            break;
    }
}

void Egraph::undoAddForbidList(Enode & to, const Enode & from) {
    // Restore forbid list for x and y
    if ( (to.getForbid( ) == from.getForbid() ) && to.getForbid() != ELRef_Undef ) {
        forbid_allocator.removeRef(to.getERef(), to.getForbid());
        to.setForbid( ELRef_Undef );
    }
        // Unsplice back the two lists
    else if ( from.getForbid( ) != ELRef_Undef ) {
        ELRef tmp = forbid_allocator[to.getForbid()].link;
        forbid_allocator[to.getForbid()].link = forbid_allocator[from.getForbid()].link;
        forbid_allocator[from.getForbid()].link = tmp;
    }

}

void Egraph::undoUpdateConstantInfo(Enode & to, Enode & from) {
    if (from.getConstant() != PTRef_Undef) {
        PTRef yc = from.getConstant();
        PTRef xc = to.getConstant();
        assert( yc == xc );
        // Invariant: the constant comes from one class only
        // No merge can occur beteween terms that point to the
        // same constant, as they would be in the same class already
//        assert( ( yc->getRoot( ) == y && xc->getRoot( ) != x )
//             || ( yc->getRoot( ) != y && xc->getRoot( ) == x ) );
        // Determine from which class the constant comes from
        if ( enode_store[yc].getRoot() == from.getERef() )
            to.clearConstant();
        else
            from.clearConstant();
    }
}

void Egraph::reinsertSignatures(ERef node) {
    ERef p = getEnode(node).getParent( );
    if (p == ERef_Undef) return;
    const bool scdr = getEnode(node).isList( );
    const ERef pstart = p;
    while (true) {
        Enode& en_p = enode_store[p];
        assert( en_p.isTerm( ) || en_p.isList( ) );

        ERef cg = en_p.getCgPtr();
        Enode& en_cg = enode_store[cg];
        // If p is a congruence root
        if ( p == cg
             || enode_store[en_p.getCar()].getRoot() != enode_store[en_cg.getCar()].getRoot()
             || enode_store[en_p.getCdr()].getRoot() != enode_store[en_cg.getCdr()].getRoot() )
        {
            en_p.setCgPtr(p);
        }
        if (en_p.getCgPtr() == p) {
#ifdef VERBOSE_EUF
            if (enode_store.containsSig(p)) {
                char* errmsg = enode_store.printEnode(p);
                cerr << errmsg;
                free(errmsg);
                assert(false);
            }
#else
//            assert(!enode_store.containsSig(p));
#endif
//            enode_store.insertSig(p);
            assert(enode_store.containsSig(p));
        }
        // Next element
        p = scdr ? en_p.getSameCdr( ) : en_p.getSameCar();
        // End of cycle
        if ( p == pstart )
            break;
    }
}
