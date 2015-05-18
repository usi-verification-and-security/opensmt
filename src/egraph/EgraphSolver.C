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
#include "SimpSMTSolver.h"
#include "TreeOps.h"

#define VERBOSE 0

//
// Checks for consistency in theories
// Shouldn't this be done elsewhere?
bool Egraph::check( bool complete )
{
  bool res = true;

  // Assert literal in the other theories
//  for ( uint32_t i = 1 ; i < tsolvers.size_( ) && res ; i ++ )
//  {
//    OrdinaryTSolver & t = *tsolvers[ i ];
//#ifdef STATISTICS
//    TSolverStats & ts = *tsolvers_stats[ i ];
//#endif
//
//#ifdef STATISTICS
//    size_t deductions_old = deductions.size( );
//#endif
//
//    res = t.check( complete );
//    if ( !res ) conf_index = i;
//
//#ifdef STATISTICS
//    if ( res )
//    {
//      ts.sat_calls ++;
//      ts.deductions_done += deductions.size( ) - deductions_old;
//    }
//    else
//      ts.uns_calls ++;
//#endif
//  }
//
//  assert( !res || explanation.size() == 0 );
//  assert( exp_cleanup.size() == 0 );

  return res;
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

  // Push ordinary theories
  for ( uint32_t i = 1 ; i < tsolvers.size_( ) ; i ++ )
    tsolvers[ i ]->pushBacktrackPoint( );

  deductions_lim .push( deductions.size( ) );
  deductions_last.push( deductions_next );
  assert( deductions_last.size( ) == deductions_lim.size( ) );
}

//
// Pops a backtrack point
//
void Egraph::popBacktrackPoint() {
    assert( backtrack_points.size( ) > 0 );
    size_t undo_stack_new_size = backtrack_points.last();
    backtrack_points.pop();
    backtrackToStackSize( undo_stack_new_size );

    // Pop ordinary theories
    for ( uint32_t i = 1 ; i < tsolvers.size_( ) ; i ++ )
        tsolvers[ i ]->popBacktrackPoint( );

    assert( deductions_last.size( ) > 0 );
    assert( deductions_lim.size( ) > 0 );
    // Restore deduction next
    deductions_next = deductions_last.last();
    deductions_last.pop();
    // Restore deductions
    size_t new_deductions_size = deductions_lim.last( );
    deductions_lim.pop( );
    while( deductions.size_() > new_deductions_size ) {
        PtAsgn_reason asgn = deductions.last();
        ERef e = enode_store.termToERef[asgn.tr];
        Enode& en_e = enode_store[e];
        assert( en_e.isDeduced() );
#ifdef VERBOSE_EUF
        cerr << "Clearing deduction " << logic.printTerm(asgn.tr) << endl;
#endif
        en_e.resetDeduced();
        deductions.pop();
    }
    assert( deductions_next <= deductions.size_() );
    assert( deductions_last.size( ) == deductions_lim.size( ) );
}

//
// Returns a deduction
//
PtAsgn_reason& Egraph::getDeduction( ) {

#ifdef VERBOSE_EUF
    cerr << "deductions available: " << deductions.size() - deductions_next << endl;
#endif
    // Communicate UF deductions
    while ( deductions_next < deductions.size_( ) ) {
        PtAsgn_reason& pta = deductions[deductions_next++];
        ERef e             = enode_store.termToERef[pta.tr];
        Enode& en_e        = enode_store[e];
        // For sure this has a deduced polarity
        assert( en_e.isDeduced( ) );
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
  while ( !suggestions.size() == 0 )
  {
    PTRef tr = suggestions.last();
    ERef e = enode_store.termToERef[tr];
    suggestions.pop();
    Enode& en_e = enode_store[e];
    if ( hasPolarity(tr) )
      continue;
    if ( en_e.isDeduced( ) )
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

#ifdef PRODUCE_PROOF
Enode * Egraph::getInterpolants( logic_t & l )
{
  assert( config.produce_inter );
  assert( 0 <= conf_index && conf_index < (int)tsolvers.size( ) );
  if ( conf_index == 0 ) 
  {
    l = QF_UF;
    return interpolants;
  }
  return tsolvers[ conf_index ]->getInterpolants( l );
}
#endif

#ifndef SMTCOMP
//void Egraph::computeModel( )
//{
//  model_computed = true;
//  //
//  // Compute models in tsolvers
//  //
//  for( unsigned i = 1 ; i < tsolvers.size( ) ; i ++ )
//    tsolvers[ i ]->computeModel( );
//  //
//  // Compute values for variables removed
//  // during preprocessing, starting from
//  // the last
//  //
//  for ( int i = top_level_substs.size( ) - 1 ; i >= 0 ; i -- )
//  {
//    Enode * var = top_level_substs[i].first;
//    Enode * term = top_level_substs[i].second;
//    Real r;
//    // Compute value for term
//    evaluateTerm( term, r );
//    // Set value for variable
//    var->setValue( r );
//  }
//}

//void Egraph::printModel( ostream & os )
//{
//  assert( config.produce_models );
//  computeModel( );
//  //
//  // Print values
//  //
//  for( set< Enode * >::iterator it = variables.begin( )
//      ; it != variables.end( )
//      ; it ++ )
//  {
//    // Retrieve enode
//    Enode * v = *it;
//    // Print depending on type
//    if ( v->hasSortBool( ) )
//      continue;
//    else if ( v->hasSortInt( )
//	   || v->hasSortReal( ) )
//    {
//      os << "(= " << v << " ";
//      if ( v->hasValue( ) )
//	os << v->getValue( );
//      else
//	os << "?";
//      os << ")";
//    }
//    else if ( config.logic == QF_UF )
//    {
//      os << "(= " << v << " " << v->getRoot( ) << ")";
//    }
//    else if ( config.logic == QF_CT )
//    {
//      os << "(= " << v << " " << v->getValue( ) << ")";
//    }
//    else
//    {
//      opensmt_error2( "model printing unsupported for this variable: ", v );
//    }
//
//    os << endl;
//  }
//}
#endif

//
// No recursion here, we assume the caller has already introduced the
// subterms
//
void Egraph::declareTerm(PtChild ptc) {
    PTRef tr = ptc.tr;

    if (!enode_store.termToERef.contains(tr)) {
        Pterm& tm = term_store[tr];
        ERef sym = enode_store.addSymb(tm.symb());
        ERef cdr = ERef_Nil;
        for (int j = tm.size()-1; j >= 0; j--) {
#ifdef VERBOSE_EUF
//            assert( checkParents(cdr) );
#endif
            ERef car = enode_store.termToERef[tm[j]];
#ifdef VERBOSE_EUF
            ERef prev_cdr = cdr;
            assert (enode_store[car].getRoot() == car);
            assert (enode_store[cdr].getRoot() == cdr);
#endif
            cdr = enode_store.addList(car, cdr);
#ifdef VERBOSE_EUF
            assert( checkParents( car ) );
            assert( checkParents( prev_cdr ) );
            assert( checkParents( cdr ) );
            assert( checkInvariants( ) );
#endif
        }
        // Canonize the term representation
#ifdef VERBOSE_EUF
        cerr << "EgraphSolver: Adding term " << logic.printTerm(tr) << " (" << tr.x << ")" << endl;
#endif
        PTRef rval = enode_store.addTerm(sym, cdr, tr);
        if (rval != tr) {
            ptc.tr = rval;
            if (ptc.parent != PTRef_Undef)
                term_store[ptc.parent][ptc.pos] = ptc.tr;
        }
//        assert (rval == tr);
    }

    // Check if termToERef contained the ref and it has been rewritten
    // to another term.  This is a bit messy, but will do for now...
    PTRef out = enode_store[enode_store.termToERef[ptc.tr]].getTerm();
    if (out != ptc.tr) {
        ptc.tr = out;
        if (ptc.parent != PTRef_Undef)
            term_store[ptc.parent][ptc.pos] = out;
    }
    if (logic.isDisequality(ptc.tr) && !enode_store.dist_classes.contains(ptc.tr))
        enode_store.addDistClass(ptc.tr);

}

// Declare a tree of terms
void Egraph::declareTermTree(PTRef tr)
{
    vec<PtChild> terms;
    getTermList(tr, terms, logic);
    for (int i = 0; i < terms.size(); i++)
        declareTerm(terms[i]);
}

// Not used
//lbool Egraph::addTerm(PTRef term, vec<PtPair>& ites, vec<PTRef>& nested_bools) {
//    assert(false);
//    assert( logic.isTheoryTerm(term) );
//    // In general we don't want to put the Boolean equalities to UF
//    // solver.  However, the Boolean uninterpreted functions are an
//    // exception.
////    assert( sym_store[t.symb()][0] != logic.getSort_bool() );
//
//    assert(logic.isEquality(term_store[term].symb())    ||
//           logic.isDisequality(term_store[term].symb()) ||
//           logic.isUP(term));
//
//    Pterm& t = term_store[term];
//
//    // Remove trivially true equalities
//    if (logic.isEquality(t.symb())) {
//        PTRef p; int i, j;
//        for (i = j = 0, p = PTRef_Undef; i < t.size(); i++)
//            if (t[i] != p)
//                t[j++] = p = t[i];
//        if (j == 1) {
//            term_store.free(term); // Lazy free
//            return l_True;
//        }
//        // shrink the size!
//        t.shrink(i-j);
//#ifdef VERBOSE_EUF
//        if (i-j != 0)
//            cout << term_store.printTerm(term) << endl;
//#endif
//    }
//    // Remove false disequalities
//    else if (logic.isDisequality(term_store[term].symb())) {
//        PTRef p; int i, j;
//        for (i = j = 0, p = PTRef_Undef; i < t.size(); i++)
//            if (t[i] == p) {
//                term_store.free(term);
//                return l_False;
//            }
//    }
//
//    vec<PtChild> queue;
//    queue.push(PtChild(term, PTRef_Undef, -1));
//    vec<PtChild> to_process;
//    PTRef rval;
//
//    // Go through the term and sort its subterms to a list
//    // from leaves to root.  Convert ITEs to conditional equalities.
//    while (queue.size() != 0) {
//        PtChild& child = queue.last();
//        PTRef tr = child.tr;
//        if (!logic.isTheoryTerm(tr))
//            nested_bools.push(tr);
//        assert(logic.isTheoryTerm(tr));
//        queue.pop();
//#ifdef VERBOSE_EUF
//        cerr << "Considering term " << term_store.printTerm(tr) << endl;
//#endif
//        SymRef sym = term_store[tr].symb();
////        if (!logic.isEquality(sym) && !logic.isDisequality(sym))
//        to_process.push(child);
//        if (logic.isDisequality(sym))
//            enode_store.addDistClass(tr);
//
//        Pterm& tm = term_store[tr];
//        for (int i = 0; i < tm.size(); i++) {
//            if (logic.isIte(term_store[tm[i]].symb())) {
//                // (1) Add a new term o_ite with no arguments and same sort as tm[i]
//                // (2) add tm[i] to ites
//                // (3) replace tm[i] with o_ite
//                SRef sr = sym_store[term_store[tm[i]].symb()].rsort();
//                vec<SRef> sort_args;
//                sort_args.push(sr);
//                char* name = NULL;
//                asprintf(&name, ".oite%d", tm[i].x);
//                const char* msg;
//                SymRef sym = sym_store.newSymb(name, sort_args, &msg);
//                // The symbol might already be there
//                if (sym == SymRef_Undef) {
//                    assert(sym_store.nameToRef(name).size() == 1);
//                    sym = sym_store.nameToRef(name)[0];
//                }
//                vec<PTRef> tmp;
//                PTRef o_ite = logic.insertTerm(sym, tmp, &msg);
//                assert(o_ite != PTRef_Undef);
//                // The old term goes to PtPair
//                ites.push(PtPair(tm[i], o_ite));
//#ifdef VERBOSE_EUF
//                cerr << "Added the term " << term_store.printTerm(tm[i], true) << " to later processing" << endl;
//                cerr << "; changing " << term_store.printTerm(tr) << " to ";
//#endif
//                tm[i] = o_ite;
//#ifdef VERBOSE_EUF
//                cerr << term_store.printTerm(tr) << endl;
//#endif
//            }
//            queue.push(PtChild(tm[i], tr, i));
//        }
//    }
//
//#ifdef VERBOSE_EUF
//    bool new_terms = false;
//#endif
//
//    // construct an enode term for each term in to_process
//    // Normalize the terms so that there will be no two UF terms with the
//    // same name.
//    for (int i = to_process.size() - 1; i >= 0; i--) {
//        PtChild& child = to_process[i];
//        PTRef tr = child.tr;
//        PTRef parent = child.parent;
//        int child_pos = child.pos;
//#ifdef VERBOSE_EUF
//        if (parent != PTRef_Undef)
//            cerr << "Now constructing / normalizing term " << term_store.printTerm(tr, true)
//                 << " which is child nr " << child_pos << " of " << term_store.printTerm(parent, true) << endl;
//        else
//            cerr << "Now constructing / normalizing term " << term_store.printTerm(tr, true) << endl;
//
//#endif
//        if (!enode_store.termToERef.contains(tr)) {
//#ifdef VERBOSE_EUF
//            new_terms = true;
//#endif
//            Pterm& tm = term_store[tr];
//            ERef sym = enode_store.addSymb(tm.symb());
//            ERef cdr = ERef_Nil;
//            for (int j = tm.size()-1; j >= 0; j--) {
//#ifdef VERBOSE_EUF
//                assert( checkParents(cdr) );
//#endif
//                ERef car = enode_store.termToERef[tm[j]];
//#ifdef VERBOSE_EUF
//                ERef prev_cdr = cdr;
//                assert (enode_store[car].getRoot() == car);
//                assert (enode_store[cdr].getRoot() == cdr);
//#endif
//                cdr = enode_store.addList(car, cdr);
//#ifdef VERBOSE_EUF
//                assert( checkParents( car ) );
//                assert( checkParents( prev_cdr ) );
//                assert( checkParents( cdr ) );
//                assert( checkInvariants( ) );
//#endif
//            }
//            // Canonize the term representation
//            rval = enode_store.addTerm(sym, cdr, tr);
//            if (rval != tr) {
//                // This is already done at term instertion time
//                assert(false);
//#ifdef VERBOSE_EUF
//                cout << "Duplicate: " << term_store.printTerm(rval)
//                     << " equals " << term_store.printTerm(tr) << endl;
//                ERef tr_new = enode_store.termToERef[rval];
//                assert( checkParents( tr_new ) );
//                assert( checkInvariants( ) );
//#endif
//                // Fix the parent term to point to the canonical
//                // representative of the child term.
//                if (child.parent != PTRef_Undef)
//                    term_store[child.parent][child_pos] = rval;
//            }
//        }
//        else {
//            assert(tr == enode_store.ERefToTerm[enode_store.termToERef[tr]]);
//            rval = tr;
//            if (child.parent != PTRef_Undef)
//                term_store[child.parent][child_pos] = tr;
//        }
//    }
//
//#ifdef VERBOSE_EUF
////    if (not new_terms)
////        cout << "All was seen" << endl;
//#endif
//    return l_Undef;
//}


lbool Egraph::addEquality(PtAsgn pa) {
    Pterm& pt = term_store[pa.tr];
    assert(pt.size() == 2);
    if (enode_store[pa.tr].isDeduced() && enode_store[pa.tr].getDeduced() == pa.sgn) {
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
        tsolver_stats.uns_calls++;
    // The sat_calls is increased already in addTrue
#endif

    return res == false ? l_False : l_Undef;
}

lbool Egraph::addDisequality(PtAsgn pa) {
    Pterm& pt = term_store[pa.tr];
    bool res = true;

    if (enode_store[pa.tr].isDeduced() && enode_store[pa.tr].getDeduced() == pa.sgn) {
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
        tsolver_stats.uns_calls++;
    // The sat_calls is increased already in addFalse
#endif

    return res == false ? l_False : l_Undef;
}

bool Egraph::addTrue(PTRef term) {
    if (enode_store[term].isDeduced() && enode_store[term].getDeduced() == l_True) {
#ifdef VERBOSE_EUF
        cerr << "Assertion already deduced: " << logic.printTerm(term) << endl;
#endif
        return true;
    }
    bool res = assertEq(term, logic.getTerm_true(), PtAsgn(term, l_True));
#ifdef STATISTICS
    if (res == false)
        tsolver_stats.uns_calls++;
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
    if (enode_store[term].isDeduced() && enode_store[term].getDeduced() == l_False) {
#ifdef VERBOSE_EUF
        cerr << "Assertion already deduced: " << logic.printTerm(term) << endl;
#endif
        return true;
    }
    bool res = assertEq(term, logic.getTerm_false(), PtAsgn(term, l_False));
#ifdef STATISTICS
    if (res == false)
        tsolver_stats.uns_calls++;
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
    ERef x = enode_store.termToERef[tr_x];
    ERef y = enode_store.termToERef[tr_y];

    Enode& en_x = enode_store[x];
    Enode& en_y = enode_store[y];
    assert( en_x.isTerm() );
    assert( en_y.isTerm() );
    assert( pending.size() == 0 );
//    assert( x->isAtom( )
//         || config.logic != QF_BV
//         || x->getWidth( ) == y->getWidth( ) );

    pending.push( x );
    pending.push( y );

#if defined(VERBOSE_EUF)
    cerr << "this is assertEq for " << logic.printTerm(en_x.getTerm())
         << " (enode-id " << tr_x.x << ") and "
         << logic.printTerm(en_y.getTerm()) << " (enode-id " << tr_y.x << ")" << endl;
#endif
#if defined(VERBOSE_EUF) && defined(CUSTOM_EL_ALLOC)
    ELRef elr_x = en_x.getForbid();
    ERef first_x = ERef_Undef;
    if (elr_x == ELRef_Undef)
        cerr << "asserting eq, x's forbid list is undef" << endl;
    else {
        cerr << "asserting eq, x's forbid list is " << endl;
        cerr << printDistinctionList(elr_x, forbid_allocator, false);
    }
    ELRef elr_y = en_y.getForbid();
    ERef first_y = ERef_Undef;
    if (elr_y == ELRef_Undef)
        cerr << "asserting eq, y's forbid list is undef" << endl;
    else {
        cerr << "asserting eq, y's forbid list is " << endl;
        cerr << printDistinctionList(elr_y, forbid_allocator, false);
    }
#elif defined(VERBOSE_EUF)
    Elist* el_x = en_x.getForbid();
    ERef first_x = ERef_Undef;
    if (el_x == NULL)
        cerr << "asserting eq, x's forbid list is undef" << endl;
    else {
        cerr << "asserting eq, x's forbid list is " << endl;
        cerr << printDistinctionList(el_x);
    }
    Elist* el_y = en_y.getForbid();
    ERef first_y = ERef_Undef;
    if (el_y == NULL)
        cerr << "asserting eq, y's forbid list is undef" << endl;
    else {
        cerr << "asserting eq, y's forbid list is " << endl;
        cerr << printDistinctionList(el_y);
    }
#endif

    const bool res = mergeLoop( r );

    return res;
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
        Enode& en_p = enode_store[p];
        Enode& en_q = enode_store[q];

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
        // Conflict detected. We should retrieve the explanation
        // We have to distinguish 2 cases. If the reason for the
        // conflict is ERef_Undef, it means that a conflict arises because
        // we tried to merge two classes that are assigned to different
        // constants, otherwise we have a proper reason
        PTRef reason_1 = PTRef_Undef;
        PTRef reason_2 = PTRef_Undef;
        //
        // Different constants
        //
        ERef enr_proot = en_p.getRoot();
        ERef enr_qroot = en_q.getRoot();

        if ( reason_inequality.tr == PTRef_Undef ) {
            Enode& en_proot = enode_store[enr_proot];
            Enode& en_qroot = enode_store[enr_qroot];
            assert(en_proot.getConstant() != PTRef_Undef);
            assert(en_qroot.getConstant() != PTRef_Undef);
            assert(enr_proot != enr_qroot);
#ifdef PRODUCE_PROOF
            if ( config.produce_inter > 0 ) {
                cgraph.setConf( p->getRoot( )->getConstant( )
                        , q->getRoot( )->getConstant( )
                        , NULL );
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
            exp_pending.push( en_p.getTerm() );
            exp_pending.push( en_proot.getConstant() );
            // 2. why q and q->constant are equal
#ifdef VERBOSE_EUF
            cerr << "constant pushing (2): "
                 << logic.printTerm(en_q.getTerm()) << " and "
                 << logic.printTerm(en_qroot.getConstant()) << endl;
#endif
            exp_pending.push( en_q.getTerm() );
            exp_pending.push( en_qroot.getConstant() );
            // 3. why p and q are equal
#ifdef VERBOSE_EUF
            cerr << "constant pushing (3): "
                 << logic.printTerm(en_q.getTerm()) << " and "
                 << logic.printTerm(en_p.getTerm()) << endl;
#endif
            exp_pending.push( en_q.getTerm() );
            exp_pending.push( en_p.getTerm() );
#ifdef VERBOSE_EUF
            cerr << "Explain XXX" << endl;
#endif
            initDup1( );
            expExplain( );
            doneDup1( );
            expCleanup(); // Should be organized better...
        }
        // Does the reason term correspond to disequality symbol
        else if ( logic.isDisequality(term_store[reason_inequality.tr].symb()) ) {
            // The reason is a distinction, but skip the false equality
            if (reason_inequality.tr != Eq_FALSE)
                explanation.push( reason_inequality );
            // We should iterate through the elements
            // of the distinction and find which atoms
            // are causing the conflict
            Pterm& pt_reason = term_store[reason_inequality.tr];
            for (int i = 0; i < pt_reason.size(); i++) {
                // (1) Get the proper term reference from pos i in the distinction
                // (2) Get the enode corresponding to the proper term
                // (3) Find the enode corresponding to the root
                // (4) Check if the root enode is the same as the root of p or q

                PTRef ptr_arg = pt_reason[i];                             // (1)
                ERef  enr_arg = enode_store.termToERef[ptr_arg];          // (2)
                ERef  enr_arg_root = enode_store[enr_arg].getRoot();      // (3)

                // (4)
                if ( enr_arg_root == enr_proot ) { assert( reason_1 == PTRef_Undef ); reason_1 = ptr_arg; }
                if ( enr_arg_root == enr_qroot ) { assert( reason_2 == PTRef_Undef ); reason_2 = ptr_arg; }
            }
            assert( reason_1 != PTRef_Undef );
            assert( reason_2 != PTRef_Undef );
#ifdef VERBOSE_EUF
            cerr << "Explain YYY" << endl;
#endif
#ifdef PRODUCE_PROOF
            expExplain( reason_1, reason_2, reason_inequality );
#else
            expExplain( reason_1, reason_2 );
#endif
        }
        else if ( logic.isEquality(term_store[reason_inequality.tr].symb()) ) {
            // The reason is a negated equality
            assert(reason_inequality.sgn == l_False);
#ifdef VERBOSE_EUF
            cerr << "Reason inequality " << logic.printTerm(reason_inequality.tr) << endl;
#endif
            Pterm& pt_reason = term_store[reason_inequality.tr];

            // Hmm, the difference being?
//          if ( config.incremental ) {
//              Enode * s = reason;
//              explanation.push_back( s );
//          }
//          else
//              explanation.push_back( reason );

            if (reason_inequality.tr != Eq_FALSE)
                explanation.push(reason_inequality);

            // The equality
            // If properly booleanized, the left and righ sides of equality
            // will always be UF terms
            // The left hand side of the equality
            reason_1 = pt_reason[0];
            // The rhs of the equality
            reason_2 = pt_reason[1];

            assert( reason_1 != PTRef_Undef );
            assert( reason_2 != PTRef_Undef );

//#if VERBOSE
#ifdef VERBOSE_EUF
//            cerr << "Reason is neg equality: " << term_store.printTerm(reason_inequality.tr) << endl;
#endif
//#endif
#ifdef VERBOSE_EUF
            cerr << "Explain ZZZ " << logic.printTerm(reason_1) << " " << logic.printTerm(reason_2) << " " << logic.printTerm(reason_inequality.tr) << endl;
#endif
#ifdef PRODUCE_PROOF
            expExplain( reason_1, reason_2, reason_inequality );
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
#endif
#ifdef GC_DEBUG
    cerr << "Asserting distinction of " << logic.printTerm(x)
         << " and " << logic.printTerm(y)
         << " enforced by " << (r.sgn == true ? "" : "not ")
         << logic.printTerm(r.tr) << endl;
#endif
#ifdef CUSTOM_EL_ALLOC
    checkFaGarbage();
#endif
#ifdef GC_DEBUG
    checkRefConsistency();
#endif
#if MORE_DEDUCTIONS
    neq_list.push_back( r );
    undo_stack_oper.push_back( ASSERT_NEQ );
    undo_stack_term.push_back( r );
#endif

    ERef p = enode_store[enode_store.termToERef[x]].getRoot();
    ERef q = enode_store[enode_store.termToERef[y]].getRoot();

    // They can't be different if the nodes are in the same class
    if ( p == q ) {
        if (r.tr != Eq_FALSE) explanation.push( r );
#ifdef VERBOSE_EUF
        cerr << "Explain XXY" << endl;
#endif
#ifdef PRODUCE_PROOF
        expExplain( x, y, r );
#else
        expExplain( x, y );
#endif

#ifdef VERBOSE_EUF
        assert( checkExp( ) );
#endif
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
#ifdef CUSTOM_EL_ALLOC
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
#else
    Elist* pdist = NULL;
    Enode& en_q = enode_store[q];
    if ( en_q.getForbid() == NULL ) {
        pdist = new Elist(p, r);
        en_q.setForbid(pdist);
        pdist->link = pdist;
    }
#endif

    // Otherwise we should put the new node after the first
    // and make the first point to pdist. This is because
    // the list is circular, but could be empty. Therefore
    // we need a "reference" element for keeping it circular.
    // So the last insertion is either the second element or
    // the only present in the list
    else {
#ifdef CUSTOM_EL_ALLOC
        pdist = forbid_allocator.alloc(p, r, ERef_Undef);
        forbid_allocator[pdist].link = forbid_allocator[en_q.getForbid()].link;
        forbid_allocator[en_q.getForbid()].link = pdist;
#ifdef GC_DEBUG
        cerr << "Added distinction " << pdist.x << endl;
        cerr << printDistinctionList(en_q.getForbid(), forbid_allocator);
        checkRefConsistency();
#endif
#else
        pdist = new Elist(p, r);
        pdist->link = en_q.getForbid()->link;
        en_q.getForbid()->link = pdist;
#endif
    }

    // Create new distinction in p
#ifdef CUSTOM_EL_ALLOC
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
#else // CUSTOM_EL_ALLOC
    Elist* qdist = NULL;
    Enode& en_p = enode_store[p];
    if ( en_p.getForbid() == NULL ) {
        qdist = new Elist(q, r);
        en_p.setForbid( qdist );
        qdist->link = qdist;
    }
    else {
        qdist = new Elist(q, r);
        qdist->link = en_p.getForbid()->link;
        en_p.getForbid()->link = qdist;
    }
#endif
    // Save operation in undo_stack
    undo_stack_main.push( Undo(DISEQ, q) );
#ifdef VERBOSE_EUF
#ifdef CUSTOM_EL_ALLOC
    cerr << printDistinctionList(en_q.getForbid(), forbid_allocator, false);
#else
    cerr << printDistinctionList(en_q.getForbid());
#endif
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
    Pterm& pt_d = term_store[tr_d];
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
        if ( root_to_enode.contains(root_id) ) {
            // Two equivalent nodes in the same distinction. Conflict
            if (tr_r.tr != Eq_FALSE)
                explanation.push(tr_r);
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
            expExplain( en_c.getTerm(), enode_store[p].getTerm(), tr_r );
#else
            expExplain( en_c.getTerm(), enode_store[p].getTerm() );
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
    Pterm& pt_d = term_store[tr_d];
    for (int i = 0; i < pt_d.size(); i++) {
        PTRef tr_c = pt_d[i];
        ERef er_c = enode_store.termToERef[tr_c];
        Enode& en_c = enode_store[er_c];
        assert(en_c.isTerm());
        en_c.setDistClasses( en_c.getDistClasses() & ~(SETBIT(index)) );
    }
#ifdef VERBOSE_EUF
    assert(checkInvariants());
#endif
}

//
// Backtracks stack to a certain size
//
void Egraph::backtrackToStackSize ( size_t size ) {
    // Make sure explanation is cleared
    // (might be empty, though, if boolean backtracking happens)
    explanation.clear();
    //
    // Restore state at previous backtrack point
    //
//    printf("stack size %d > %d\n", undo_stack_term.size(), size);
    while ( undo_stack_main.size_() > size ) {
        Undo& u = undo_stack_main.last();
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
        else if ( last_action == INITCONG ) {
            assert( config.isIncremental() );
#if VERBOSE
            cerr << "UNDO: BEG INITCONG " << e << endl;
#endif
            ERef e = u.arg.er;
            Enode& en_e = enode_store[e];

            ERef car = en_e.getCar( );
            ERef cdr = en_e.getCdr( );
            assert( car != ERef_Undef );
            assert( cdr != ERef_Undef );

            if ( en_e.getCgPtr( ) == e ) {
                assert( enode_store.lookupSig( e ) == e );
                // Remove from sig_tab
                enode_store.removeSig( e );
            }
            else {
                assert( enode_store.lookupSig( e ) != e );
                en_e.setCgPtr( e );
            }

            assert( initialized.find( en_e.getId( ) ) != initialized.end( ) );
            // Remove from initialized nodes
            initialized.erase( en_e.getId( ) );
            assert( initialized.find( en_e.getId( ) ) == initialized.end( ) );
            // Remove parents info
//            if ( en_e.isList( ) )
//                enode_store.removeParent( car, e );
//            enode_store.removeParent( cdr, e );

            // Deallocate congruence data
            // This sounds like a huge overhead!
//      assert( en_e.hasCongData( ) );
//      e->deallocCongData( );
//      assert( !e->hasCongData( ) );
        }
        else if ( last_action == FAKE_MERGE ) {
#if VERBOSE
            cerr << "UNDO: BEGIN FAKE MERGE " << e << endl;
#endif
            ERef e = u.arg.er;
            Enode& en_e = enode_store[e];
#ifdef VERBOSE_EUF
            cerr << "Undo fake merge: " << logic.printTerm(en_e.getTerm()) << endl;
#endif

            assert( initialized.find( en_e.getId( ) ) != initialized.end( ) );
            initialized.erase( en_e.getId( ) );
            assert( initialized.find( en_e.getId( ) ) == initialized.end( ) );
//      assert( e->hasCongData( ) );
//      e->deallocCongData( );
//      assert( !e->hasCongData( ) );
        }
        else if ( last_action == FAKE_INSERT ) {
#if VERBOSE
            cerr << "UNDO: BEGIN FAKE INSERT " << e << endl;
#endif
            ERef e = u.arg.er;
            Enode& en_e = enode_store[e];
#ifdef VERBOSE_EUF
            cerr << "Undo fake insert: " << logic.printTerm(en_e.getTerm()) << endl;
#endif

            assert( en_e.isTerm( ) || en_e.isList( ) );
            ERef car = en_e.getCar( );
            ERef cdr = en_e.getCdr( );
            assert( car != ERef_Nil );
            assert( cdr != ERef_Nil );

            // Node must be there if its a congruence
            // root and it has to be removed
            if ( en_e.getCgPtr() == e ) {
                assert( enode_store.lookupSig( e ) == e );
                enode_store.removeSig( e );
            }
            // Otherwise sets it back to itself
            else {
                assert( enode_store.lookupSig( e ) != e );
                en_e.setCgPtr( e );
            }

            // Remove Parent info
//            if ( en_e.isList( ) )
//                enode_store.removeParent( car, e );
//            enode_store.removeParent( cdr, e );
            // Remove initialization
            assert( initialized.find( en_e.getId( ) ) != initialized.end( ) );
            initialized.erase( en_e.getId( ) );
            // Dealloc cong data
//      assert( e->hasCongData( ) );
//      e->deallocCongData( );
//      assert( !e->hasCongData( ) );
        }
        else if ( last_action == DISEQ ) {
            ERef e = u.arg.er;
            Enode& en_e = enode_store[e];
            undoDisequality( e );
        }
        else if ( last_action == DIST ) {
            PTRef ptr = u.arg.ptr;
            undoDistinction( ptr );
        }
//    else if ( last_action == SYMB )
//      removeSymbol( e );
//    else if ( last_action == NUMB )
//      removeNumber( e );
        else if ( last_action == CONS )
//      undoCons( e );
//    else if ( last_action == INSERT_STORE )
//      removeStore( e );
        ;
        else
            opensmt_error( "unknown action" );
    }

}

// bool Egraph::checkDupClause( Enode * c1, Enode * c2 )
// {
//   assert( c1 );
//   assert( c2 );
//   // Swap let cl3 be the lowest clause
//   if ( c1->getId( ) > c2->getId( ) )
//   {
//     Enode * tmp = c1;
//     c1 = c2;
//     c2 = tmp;
//   }
// 
// #ifdef BUILD_64
//   enodeid_pair_t sig = encode( c1->getId( ), c2->getId( ) );
// #else
//   Pair( enodeid_t ) sig = make_pair( c1->getId( ), c2->getId( ) );
// #endif
// 
//   const bool res = clauses_sent.insert( sig ).second == false;
//   return res;
// }

//void Egraph::splitOnDemand( vector< Enode * > & c, const int
//#ifdef STATISTICS
//    id 
//#endif
//    )
//{
//  assert( config.incremental );
//  // Assume that we split only of size 2
//  assert( c.size( ) == 2 );
//  if ( checkDupClause( c[ 0 ], c[ 1 ] ) ) return;
//#ifdef STATISTICS
//  assert( id >= 0 );
//  assert( id < static_cast< int >( tsolvers_stats.size( ) ) );
//  TSolverStats & ts = *tsolvers_stats[ id ];
//  if ( (long)c.size( ) > ts.max_sod_size )
//    ts.max_sod_size = c.size( );
//  if ( (long)c.size( ) < ts.min_sod_size )
//    ts.min_sod_size = c.size( );
//  ts.sod_sent ++;
//  ts.sod_done ++;
//  ts.avg_sod_size += c.size( );
//#endif
//
//#ifdef PRODUCE_PROOF
//  assert( config.produce_inter == 0 || c[ 0 ]->getIPartitions( ) != 0 );
//  assert( config.produce_inter == 0 || c[ 1 ]->getIPartitions( ) != 0 );
//  // FIXME: should compute interpolant ...
//  solver->addSMTAxiomClause( c, NULL );
//#else
//  solver->addSMTAxiomClause( c );
//#endif
//}

//void Egraph::splitOnDemand( Enode * c, const int
//#ifdef STATISTICS
//    id 
//#endif
//    )
//{
//  assert( c );
//
//#ifdef STATISTICS
//  assert( id >= 0 );
//  assert( id < static_cast< int >( tsolvers_stats.size( ) ) );
//  TSolverStats & ts = *tsolvers_stats[ id ];
//  if ( ts.max_sod_size < 1 )
//    ts.max_sod_size = 1;
//  if ( ts.min_sod_size > 1 )
//    ts.min_sod_size = 1;
//  ts.sod_sent ++;
//  ts.sod_done ++;
//  ts.avg_sod_size ++;
//#endif
//
//  solver->addNewAtom( c );
//}

//=============================================================================
// Congruence Closure Routines

//
// Merge the class of x with the class of y
// x will become the representant
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
    assert( checkParents( x ) );
    assert( checkParents( y ) );
    assert( checkInvariants( ) );
#endif

    // This is weird.  If I get the references here and change them afterwards, the cgdata will not be correct.
    Enode& an_x = enode_store[x];
    Enode& an_y = enode_store[y];

    if (an_x.isTerm()) {
        assert( !isConstant(x) || !isConstant(y) );
        assert( !isConstant(x) || an_x.getSize() == 1 );
        assert( !isConstant(y) || an_y.getSize() == 1 );
    }
    assert( an_x.getRoot( ) != an_y.getRoot( ) );
    assert( x == an_x.getRoot( ) );
    assert( y == an_y.getRoot( ) );

  // Swap x,y if y has a larger eq class
    if ( an_x.getSize() < an_y.getSize()
        || (an_x.isTerm() && isConstant(x)) )
    {
        ERef tmp = x;
        x = y;
        y = tmp;
    }
    // Get the references right here
    Enode& en_x = enode_store[x];
    Enode& en_y = enode_store[y];

    assert(en_x.type() == en_y.type());
    assert(!en_x.isTerm() || !isConstant(x));

    // TODO:
    // Propagate equalities to other ordinary theories
    //

    // Update forbid list for x by adding elements of y
#ifdef CUSTOM_EL_ALLOC
    if ( en_y.getForbid( ) != ELRef_Undef ) {
        // We assign the same forbid list
        if ( en_x.getForbid( ) == ELRef_Undef ) {
            en_x.setForbid( en_y.getForbid( ) );
            forbid_allocator.addReference(en_x.getForbid(), x);
        }
        // Otherwise we splice the two lists
        else {
            ELRef tmp = forbid_allocator[en_x.getForbid()].link;
            forbid_allocator[en_x.getForbid()].link = forbid_allocator[en_y.getForbid()].link;
            forbid_allocator[en_y.getForbid()].link = tmp;
        }
    }
#ifdef GC_DEBUG
    checkRefConsistency();
    checkForbidReferences(x);
#endif
#else // CUSTOM_EL_ALLOC
    if ( en_y.getForbid( ) != NULL ) {
        // We assign the same forbid list
        if ( en_x.getForbid( ) == NULL )
            en_x.setForbid( en_y.getForbid( ) );

        // Otherwise we splice the two lists
        else {
            Elist* tmp = en_x.getForbid()->link;
            en_x.getForbid()->link = en_y.getForbid()->link;
            en_y.getForbid()->link = tmp;
        }
    }
#endif // CUSTOM_EL_ALLOC
    // Merge distinction classes
    en_x.setDistClasses( ( en_x.getDistClasses( ) | en_y.getDistClasses( ) ) );
    // Assign w to the class with fewer parents
    ERef w = en_x.getParentSize() < en_y.getParentSize( ) ? x : y ;
    // Visit each parent of w, according to the type of w
    // and remove each congruence root from the signature table
    Enode& en_w = enode_store[w];
    ERef p = en_w.getParent();
    const ERef pstart = p;
    const bool scdr = en_w.isList( );
    for ( ; p != ERef_Undef ; ) {
        Enode& en_p = enode_store[p];
        assert ( en_p.isTerm( ) || en_p.isList( ) );
        // If p is a congruence root
        if ( p == en_p.getCgPtr( ) )
            enode_store.removeSig( p );
        // Next element
        p = scdr ? en_p.getSameCdr( ) : en_p.getSameCar( ) ;
        // End of cycle
        if ( p == pstart )
            p = ERef_Undef;
    }

    // Compute deductions that follows from
    // merging x and y. Probably this function
    // could be partially embedded into the next
    // cycle. However, for the sake of simplicity
    // we prefer to separate the two contexts
    if ( config.uf_theory_propagation > 0 ) {
        deduce( x, y, reason );
    }

    // Perform the union of the two equivalence classes
    // i.e. reroot every node in y's class to point to x

    ERef v = y;
    const ERef vstart = v;
#ifdef VERBOSE_EUF
    bool constant_shouldset = false;
    bool constant_set = false;
#endif
    while (true) {
        Enode& en_v = enode_store[v];
        // XXX
#ifdef VERBOSE_EUF
        if (isConstant(v)) {
            cerr << "Rerooting " << logic.printTerm(en_v.getTerm()) << endl;
            constant_shouldset = true;
        }
#endif
        en_v.setRoot(x);
        v = en_v.getNext();
        if (v == vstart)
            break;
    }

    // Splice next lists
    ERef tmp = en_x.getNext();
    en_x.setNext( en_y.getNext() );
    en_y.setNext( tmp );
    // Update size of the congruence class
    en_x.setSize( en_x.getSize( ) + en_y.getSize( ) );

    // Preserve signatures of larger parent set
    if ( en_x.getParentSize() < en_y.getParentSize() )
    {
        enodeid_t tmp = en_x.getCid();
        en_x.setCid( en_y.getCid() );
        en_y.setCid( tmp );
    }

    // Insert new signatures and propagate congruences
    p = en_w.getParent();
    for ( ; p != ERef_Undef; ) {
        Enode& en_p = enode_store[p];
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

    // Merge parent lists
    if ( en_y.getParent() != ERef_Undef ) {
        // If x has no parents, we assign y's one
        if ( en_x.getParent() == ERef_Undef ) {
            assert( en_x.type() == en_y.type() );
            en_x.setParent( en_y.getParent() );
        }
        // Splice the parent lists
        else {
            if ( en_x.isList() ) {
                ERef tmp = enode_store[en_x.getParent()].getSameCdr();
                enode_store[en_x.getParent()].setSameCdr( enode_store[en_y.getParent()].getSameCdr( ) );
                enode_store[en_y.getParent()].setSameCdr( tmp );
            }
            else {
                ERef tmp = enode_store[en_x.getParent()].getSameCar();
                enode_store[en_x.getParent()].setSameCar( enode_store[en_y.getParent()].getSameCar() );
                enode_store[en_y.getParent()].setSameCar( tmp );
            }
        }
    }
    // Adjust parent size
    en_x.setParentSize( en_x.getParentSize( ) + en_y.getParentSize( ) );
#ifdef VERBOSE_EUF
    checkParents(x);
#endif
    // Store info about the constant
    if (en_y.isTerm() && en_y.getConstant() != PTRef_Undef) {
        assert(en_x.getConstant() == PTRef_Undef);
        en_x.setConstant( en_y.getConstant() );
#ifdef VERBOSE_EUF
        constant_set = true;
#endif
    }
    // Store info about the constant
    else if (en_x.isTerm() && en_x.getConstant() != PTRef_Undef) {
        assert(en_y.getConstant() == PTRef_Undef);
        en_y.setConstant(en_x.getConstant());
#ifdef VERBOSE_EUF
        constant_set = true;
#endif
    }

#ifdef VERBOSE_EUF
    if (constant_shouldset && !constant_set)
        assert(false);
#endif

  // Push undo record
    undo_stack_main.push( Undo(MERGE,y) );
#ifdef VERBOSE_EUF
    undo_stack_main.last().merged_with = x;
    undo_stack_main.last().bool_term = reason.tr;
#endif

//    if (en_x.isTerm()) {
//        printf("Merging %s and %s, undo stack size %d\n", term_store.printTerm(en_x.getTerm()), term_store.printTerm(en_y.getTerm()), undo_stack_term.size());
//        printf("There are %d backtrack points\n", backtrack_points.size());
//    }

#ifdef VERBOSE_EUF
    assert( checkParents( x ) );
    assert( checkParents( y ) );
    assert( checkInvariants( ) );
#endif
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
                if (eq != PTRef_Undef && enode_store.termToERef.contains(eq)) {
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
//        assert(!enode_store[sv].hasPolarity());
        if (!enode_store[sv].isDeduced()) { // Can be previously deduced with the negative deduction engine
//            if ( !enode_store[sv].hasPolarity() && !enode_store[sv].isDeduced()
            if ( !hasPolarity(enode_store[sv].getTerm()) && !enode_store[sv].isDeduced()
//              && enode_store[sv].getTerm() != enode_store[x].getTerm()
//              && enode_store[sv].getTerm() != enode_store[y].getTerm()
                // Also when incrementality is used, node should be explicitly informed
//              && ( config.isIncremental == false || informed.contains(enode_store[sv].getId()))
               )
            {
                enode_store[sv].setDeduced(deduced_polarity);
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
                deductions.push(PtAsgn_reason(enode_store.ERefToTerm[sv],
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
#ifdef VERBOSE_EUF
    assert( checkInvariants( ) );
#endif
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
    cerr << "Undo merge of " << y.x << endl;
#endif
    assert( y != ERef_Undef );

    Enode& en_y = enode_store[y];

    // x is the node that was merged with y
    ERef x = en_y.getRoot( );

    assert( x != ERef_Undef );

    Enode& en_x = enode_store[x];

#if VERBOSE
//    cerr << "UM: Undoing merge of " << y << " and " << x << endl;
#endif
#if VERBOSE_EUF
//    if (en_y.isTerm())
//        cerr << "UM: Undoing merge of " << logic.printTerm(en_y.getTerm())
//             << " and " << logic.printTerm(en_x.getTerm()) << endl;
#endif

    // Undoes the merge of the parent lists
    en_x.setParentSize( en_x.getParentSize() - en_y.getParentSize() );
    // Restore the correct parents
    if ( en_y.getParent( ) != ERef_Undef ) {
        // If the parents are equal, that means that
        // y's parent has been assigned to x
        if ( en_x.getParent( ) == en_y.getParent( ) )
            en_x.setParent( ERef_Undef );
        // Unsplice the parent lists
        else {
            assert( en_x.getParent() != ERef_Undef );
            if ( en_x.isList( ) ) {
                ERef tmp = enode_store[en_x.getParent()].getSameCdr();
                enode_store[en_x.getParent()].setSameCdr( enode_store[en_y.getParent()].getSameCdr() );
                enode_store[en_y.getParent()].setSameCdr( tmp );
            }
            else {
                ERef tmp = enode_store[en_x.getParent()].getSameCar();
                enode_store[en_x.getParent()].setSameCar( enode_store[en_y.getParent()].getSameCar() );
                enode_store[en_y.getParent()].setSameCar( tmp );
            }
        }
    }

    // Assign w to the smallest parent class
    ERef w = en_x.getParentSize( ) < en_y.getParentSize( ) ? x : y ;
    assert(w != ERef_Undef);
    Enode& en_w = enode_store[w];
    // Undoes the insertion of the modified signatures
    ERef p = en_w.getParent( );
    const ERef pstart = p;
    // w might be NULL, i.e. it may not have fathers (hmm, checked for ERef_Undef above)
    const bool scdr = w == ERef_Undef ? false : en_w.isList( );

    if (p == ERef_Undef) goto skip_cgroot_sig_removal;
    while (true) {
        Enode& en_p = enode_store[p];
        assert( en_p.isTerm( ) || en_p.isList( ) );
        // If p is a congruence root
        if ( p == en_p.getCgPtr( ) ) {
            assert( enode_store.lookupSig( p ) != ERef_Undef );
            enode_store.removeSig( p );
        }
        // Next element
        p = scdr ? en_p.getSameCdr( ) : en_p.getSameCar( ) ;
        // End of cycle
        if ( p == pstart )
            break;
    }
skip_cgroot_sig_removal:
    // Restore the size of x's class
    en_x.setSize( en_x.getSize( ) - en_y.getSize( ) );
    // Unsplice next lists
    ERef tmp = en_x.getNext( );
    en_x.setNext( en_y.getNext( ) );
    en_y.setNext( tmp );
    // Reroot each node of y's eq class back to y
    ERef v = y;
    const ERef vstart = v;
    while (true) {
        Enode& en_v = enode_store[v];
        en_v.setRoot( y );
        v = en_v.getNext( );
        if ( v == vstart )
            break;
    }
    // Undo swapping
    if ( en_x.getParentSize( ) < en_y.getParentSize( ) ) {
        enodeid_t tmp = en_x.getCid( );
        en_x.setCid( en_y.getCid( ) );
        en_y.setCid( tmp );
    }
    // Reinsert back signatures that have been removed during
    // the merge operation
    p = en_w.getParent( );
    if (p == ERef_Undef) goto skip_signature_removal;
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
            assert(!enode_store.containsSig(p));
#endif
            enode_store.insertSig(p);
        }
        // Next element
        p = scdr ? en_p.getSameCdr( ) : en_p.getSameCar();
        // End of cycle
        if ( p == pstart )
            break;
    }
skip_signature_removal:
    // Restore distinction classes for x, with a set difference operation
    en_x.setDistClasses( ( en_x.getDistClasses() & ~(en_y.getDistClasses())) );

    // Restore forbid list for x and y
#ifdef CUSTOM_EL_ALLOC
    if ( (en_x.getForbid( ) == en_y.getForbid() ) && en_x.getForbid() != ELRef_Undef ) {
        forbid_allocator.removeRef(x, en_x.getForbid());
        en_x.setForbid( ELRef_Undef );
    }
    // Unsplice back the two lists
    else if ( en_y.getForbid( ) != ELRef_Undef ) {
        ELRef tmp = forbid_allocator[en_x.getForbid()].link;
        forbid_allocator[en_x.getForbid()].link = forbid_allocator[en_y.getForbid()].link;
        forbid_allocator[en_y.getForbid()].link = tmp;
    }
#else
    if ( (en_x.getForbid( ) == en_y.getForbid() ) && en_x.getForbid() != NULL )
        en_x.setForbid( NULL );
    // Unsplice back the two lists
    else if ( en_y.getForbid( ) != NULL ) {
        Elist* tmp = en_x.getForbid()->link;
        en_x.getForbid()->link = en_y.getForbid()->link;
        en_y.getForbid()->link = tmp;
    }
#endif

    if (en_y.getConstant() != PTRef_Undef) {
        PTRef yc = en_y.getConstant();
        PTRef xc = en_x.getConstant();
        assert( yc == xc );
        // Invariant: the constant comes from one class only
        // No merge can occur beteween terms that point to the
        // same constant, as they would be in the same class already
//        assert( ( yc->getRoot( ) == y && xc->getRoot( ) != x )
//             || ( yc->getRoot( ) != y && xc->getRoot( ) == x ) );
        // Determine from which class the constant comes from
        if ( enode_store[yc].getRoot() == y )
            en_x.clearConstant();
        else
            en_y.clearConstant();
    }

  //
  // TODO: unmerge for ordinary theories
  //

#ifdef VERBOSE_EUF
  assert( checkParents( y ) );
  assert( checkParents( x ) );
  assert( checkInvariants( ) );
#endif
#ifdef GC_DEBUG
    checkRefConsistency();
#endif
}

//
// Restore the state before the addition of a disequality
//
#ifdef CUSTOM_EL_ALLOC
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

#if VERBOSE
    cerr << "UD: Undoing distinction of " << x << " and " << y << endl;
#elif VERBOSE_EUF
//    if (en_x.isTerm())
//        cerr << "UD: Undoing distinction of "
//             << logic.printTerm(en_x.getTerm()) << " and "
//             << logic.printTerm(en_y.getTerm()) << endl;
#endif

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

#ifdef VERBOSE_EUF
    assert( checkInvariants( ) );
#endif
#ifdef GC_DEBUG
    checkRefConsistency();
#endif
}

#else // CUSTOM_EL_ALLOC
void Egraph::undoDisequality ( ERef x )
{
    Enode& en_x = enode_store[x];
    assert( en_x.getForbid() != NULL );

    // We have to distinguish two cases:
    // If there is only one node, that is the
    // distinction to remove
    Elist* xfirst = en_x.getForbid( );
    ERef y = ERef_Undef;
    if ( xfirst->link == xfirst )
        y = xfirst->e;
    else
        y = xfirst->link->e;

    Enode& en_y = enode_store[y];


    Elist* yfirst = en_y.getForbid();

#if VERBOSE
    cerr << "UD: Undoing distinction of " << x << " and " << y << endl;
#endif

    // Some checks
    assert( yfirst != NULL );
    assert( yfirst->link != yfirst || yfirst->e == x );
    assert( yfirst->link == yfirst || yfirst->link->e == x );
    assert( en_x.getRoot( ) != en_y.getRoot( ) );

    Elist* ydist = xfirst->link == xfirst ? xfirst : xfirst->link;

    // Only one node in the list
    if ( ydist->link == ydist )
        en_x.setForbid( NULL );
    // Other nodes in the list
    else
        xfirst->link = ydist->link;

    delete ydist;

    Elist* xdist = yfirst->link == yfirst ? yfirst : yfirst->link;

    // Only one node in the list
    if ( xdist->link == xdist ) {
        assert(en_y.getForbid() != NULL);
        en_y.setForbid( NULL );
    }
    // Other nodes in the list
    else
        yfirst->link = xdist->link;

    delete xdist;

#ifdef VERBOSE_EUF
    assert( checkInvariants( ) );
#endif
}
#endif // CUSTOM_EL_ALLOC

bool Egraph::unmergeable (ERef x, ERef y, PtAsgn& r)
{
    assert( x != ERef_Undef );
    assert( y != ERef_Undef );

    ERef p = enode_store[x].getRoot();
    ERef q = enode_store[y].getRoot();

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
    Enode& en_p = enode_store[p];
    Enode& en_q = enode_store[q];
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
#ifdef CUSTOM_EL_ALLOC
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
        Elist& el_pptr = forbid_allocator[pptr];
        Elist& el_qptr = forbid_allocator[qptr];
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

#else // CUSTOM_EL_ALLOC

    // Check forbid lists (binary distinction)
    Elist* pstart = en_p.getForbid( );
    Elist* qstart = en_q.getForbid( );
    // If at least one is empty, they can merge
    if ( pstart == NULL || qstart == NULL )
        return false;

    Elist* pptr = pstart;
    Elist* qptr = qstart;

    r = PtAsgn(PTRef_Undef, l_True);

    for (;;) {
        // They are unmergeable if they are on the other forbid list
        if ( enode_store[pptr->e].getRoot( ) == q ) {
#ifdef VERBOSE_EUF
            cerr << "Unmergeable-q: " << logic.printTerm(enode_store[q].getTerm()) << endl;
            cerr << " - reason: " << logic.printTerm(pptr->reason.tr) << endl;
#endif
            r = pptr->reason;
            return true;
        }
        if ( enode_store[qptr->e].getRoot( ) == p ) {
#ifdef VERBOSE_EUF
            cerr << "Unmergeable-p: " << logic.printTerm(enode_store[p].getTerm()) << endl;
            cerr << " - reason: " << logic.printTerm(qptr->reason.tr) << endl;
#endif
            r = qptr->reason;
            return true;
        }
        // Pass to the next element
        pptr = pptr->link;
        qptr = qptr->link;
        // If either list finishes, exit. This is ok because
        // if x is on y's forbid list, then y is on x's forbid
        // list as well
        if ( pptr == pstart ) break;
        if ( qptr == qstart ) break;
    }
#endif
    // If here they are mergable
    assert( r.tr == PTRef_Undef );
    return false;
}


#ifdef PRODUCE_PROOF
void Egraph::tmpMergeBegin( Enode * x, Enode * y )
{
  assert( config.produce_inter != 0 );
  assert( config.logic == QF_AX
       || config.logic == QF_AXDIFF );

  if ( !x->hasCongData( ) ) x->allocCongData( );
  if ( !y->hasCongData( ) ) y->allocCongData( );

  x = x->getRoot( );
  y = y->getRoot( );

  // x will become root
  // Swap x,y if x is not root
  if ( x->getRoot( ) != x )
  {
    Enode * tmp = x;
    x = y;
    y = tmp;
  }

  // Swap if y is ABcommon and x no
  if ( y->getIPartitions( ) == 6 &&
       x->getIPartitions( ) != 6 )
  {
    Enode * tmp = x;
    x = y;
    y = tmp;
  }

  Enode * v = y;
  const Enode * vstart = v;
  for (;;)
  {
    v->setRoot( x );
    v = v->getNext( );
    if ( v == vstart )
      break;
  }

  // Splice next lists
  Enode * tmp = x->getNext( );
  x->setNext( y->getNext( ) );
  y->setNext( tmp );
  // Update size of the congruence class
  x->setSize( x->getSize( ) + y->getSize( ) );
}

void Egraph::tmpMergeEnd( Enode * x, Enode * y )
{
  assert( config.produce_inter != 0 );
  assert( config.logic == QF_AX
       || config.logic == QF_AXDIFF );

  if ( x->getSize( ) < y->getSize( ) )
  {
    Enode * tmp = x;
    x = y;
    y = tmp;
  }

  // Restore the size of x's class
  x->setSize( x->getSize( ) - y->getSize( ) );
  // Unsplice next lists
  Enode * tmp = x->getNext( );
  x->setNext( y->getNext( ) );
  y->setNext( tmp );
  // Reroot each node of y's eq class back to y
  Enode * v = y;
  const Enode * vstart = v;
  for (;;)
  {
    v->setRoot( y );
    v = v->getNext( );
    if ( v == vstart )
      break;
  }

  assert( x->getRoot( ) != y->getRoot( ) );
}
#endif

//
// Functions to be used when egraph is used 
// as a supporting solver for another theory
// e.g. AX
//
//bool Egraph::extAssertLit( Enode * e )
//{
//  assert( config.uf_disable == 0 );
//  congruence_running = true;
//#ifndef SMTCOMP
//  model_computed = false;
//#endif
//
//  bool res = assertLit_( e );
//
//  return res;
//}

#if MORE_DEDUCTIONS
bool Egraph::deduceMore( vector< Enode * > & saved_deds )
{
  //
  // For each negated equality
  //
  // x != y
  //
  // we see if there are terms
  //
  // rd( a, i )
  // rd( b, j )
  //
  // such that
  //
  // x ~ rd( a, i )
  // y ~ rd( b, j )
  // a ~ b
  //
  // these relations imply that i != j,
  // which is what we (potentially create and)
  // theory-propagate
  //
  bool deduced = false;
  for ( size_t k = 0 ; k < neq_list.size( ) ; k ++ )
  {
    if ( neq_list[ k ]->get1st( )->getRetSort( ) != getSortElem( ) )
      continue;

    vector< Enode * > x_reads, y_reads;

    Enode * x = neq_list[ k ]->get1st( );
    Enode * y = neq_list[ k ]->get2nd( );

    Enode * v = x;
    const Enode * vstart = v;
    for (;;)
    {
      if ( v->isSelect( ) )
	x_reads.push_back( v );

      v = v->getNext( );
      if ( v == vstart )
	break;
    }

    Enode * t = y;
    const Enode * tstart = t;
    for (;;)
    {
      if ( t->isSelect( ) )
	y_reads.push_back( t );

      t = t->getNext( );
      if ( t == tstart )
	break;
    }

    for ( size_t x_i = 0 ; x_i < x_reads.size( ) ; x_i ++ )
    {
      for ( size_t y_i = 0 ; y_i < y_reads.size( ) ; y_i ++ )
      {
	// Check if they are equal in all but one position
	Enode * read1 = x_reads[ x_i ];
	Enode * read2 = y_reads[ y_i ];
	Enode * diff1 = NULL, * diff2 = NULL;

	if ( read1->get1st( )->getRoot( ) ==
	     read2->get1st( )->getRoot( ) )
	{
	  diff1 = x_reads[ x_i ]->get2nd( );
	  diff2 = y_reads[ y_i ]->get2nd( );
	}
	else if ( read1->get2nd( )->getRoot( ) ==
	          read2->get2nd( )->getRoot( ) )
	{
	  Enode * a1 = read1->get1st( );
	  Enode * a2 = read2->get1st( );

	  int nof_diff = 0;

	  while ( nof_diff <= 1 
	      && a1->isStore( ) 
	      && a2->isStore( ) ) 
	  {
	    if ( a1->get3rd( )->getRoot( ) !=
		 a2->get3rd( )->getRoot( ) ) 
	    {
	      // diff1 = a1->get3rd( );
	      // diff2 = a2->get3rd( );
	      // nof_diff ++;
	      // Force exit
	      nof_diff = 2;
	    }
	    if ( a1->get2nd( )->getRoot( ) !=
		 a2->get2nd( )->getRoot( ) ) 
	    {
	      diff1 = a1->get2nd( );
	      diff2 = a2->get2nd( );
	      nof_diff ++;
	    }
	    a1 = a1->get1st( );
	    a2 = a2->get1st( );
	  }

	  // Cannot be different in one
	  if ( !a1->isVar( ) || !a2->isVar( ) )
	    continue;
	  // Different in more than one place
	  if ( nof_diff > 1 )
	    continue;

	  assert( nof_diff == 1 );
	}
	else 
	{
	  continue;
	}

	assert( diff1 );
	assert( diff2 );
	assert( diff1->getRoot( ) != diff2->getRoot( ) );

	Enode * eij = mkEq( cons( diff1
	                  , cons( diff2 ) ) );
	  
	if ( eij->hasPolarity( ) 
	  || eij->isDeduced( ) )
	  continue;

	// Adds if does not exists
	splitOnDemand( eij, id );
	cerr << "DEDUCED: " << eij << endl;
	eij->setDeduced( l_False, id );
	saved_deds.push_back( eij );
	deduced = true;
#ifdef STATISTICS
	tsolvers_stats[ 0 ]->deductions_done ++;
#endif
      }
    }
  }

  return deduced;
}
#endif

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

#ifdef CUSTOM_EL_ALLOC
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
            ERef reason_lhs = enode_store.termToERef[term_store[e_new.reason.tr][0]];
            ERef reason_rhs = enode_store.termToERef[term_store[e_new.reason.tr][1]];
            assert (enode_store[reason_lhs].getRoot() != enode_store[reason_rhs].getRoot());
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

#endif
