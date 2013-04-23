/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2010, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
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
        PTRef tr = deductions.last();
        ERef e = enode_store.termToERef[tr];
        Enode& en_e = enode_store[e];
        assert( en_e.isDeduced( ) );
        deductions.pop();
    }
    assert( deductions_next <= deductions.size_() );
    assert( deductions_last.size( ) == deductions_lim.size( ) );
}

//
// Returns a deduction
//
PTRef Egraph::getDeduction( )
{
  // Communicate UF deductions
  while ( deductions_next < deductions.size_( ) )
  {
    PTRef tr = deductions[deductions_next++];
    ERef e = enode_store.termToERef[tr];
    Enode& en_e = enode_store[e];
    // For sure this has a deduced polarity
    assert( en_e.isDeduced( ) );
    // If it has been pushed it is not a good candidate
    // for deduction
    if ( en_e.hasPolarity( ) )
      continue;

#ifdef STATISTICS
//    const int index = e->getDedIndex( );
//    tsolvers_stats[ index ]->deductions_sent ++;
#endif

    return tr;
  }

  // We have already returned all the possible deductions
  return PTRef_Undef;
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
    if ( en_e.hasPolarity( ) )
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
vec<PTRef>& Egraph::getConflict( bool deduction )
{
//    assert( 0 <= conf_index && conf_index < (int)tsolvers.size( ) );
//    (void)deduction;
#ifdef STATISTICS
//    TSolverStats & ts = *tsolvers_stats[ conf_index ];
//    if ( deduction ) {
//        if ( (long)explanation.size( ) > ts.max_reas_size )
//            ts.max_reas_size = explanation.size( );
//        if ( (long)explanation.size( ) < ts.min_reas_size )
//            ts.min_reas_size = explanation.size( );
//        ts.reasons_sent ++;
//        ts.avg_reas_size += explanation.size( );
//    }
//    else {
//        if ( (long)explanation.size( ) > ts.max_conf_size )
//            ts.max_conf_size = explanation.size( );
//        if ( (long)explanation.size( ) < ts.min_conf_size )
//            ts.min_conf_size = explanation.size( );
//        ts.conflicts_sent ++;
//        ts.avg_conf_size += explanation.size( );
//    }
#endif
    return explanation;
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

PTRef Egraph::addTerm(PTRef term, vec<PtPair>& ites) {
    assert( logic.isTheoryTerm(term) );
    // In general we don't want to put the Boolean equalities to UF
    // solver.  However, the Boolean uninterpreted functions are an
    // exception.
//    assert( sym_store[t.symb()][0] != logic.getSort_bool() );

    assert(logic.isEquality(term_store[term].symb())    ||
           logic.isDisequality(term_store[term].symb()) ||
           logic.isUP(term));

    vec<PtChild> queue;
    queue.push(PtChild(term, PTRef_Undef, -1));
    vec<PtChild> to_process;
    PTRef rval;

    // Go through the term and sort its subterms to a list
    // from leaves to root.  Convert ITEs to conditional equalities.
    while (queue.size() != 0) {
        PtChild& child = queue.last();
        PTRef tr = child.tr;
        assert(logic.isTheoryTerm(tr));
        queue.pop();
#ifdef PEDANTIC_DEBUG
        cerr << "Considering term " << term_store.printTerm(tr) << endl;
#endif
        SymRef sym = term_store[tr].symb();
        if (!logic.isEquality(sym) && !logic.isDisequality(sym))
            to_process.push(child);
        if (logic.isDisequality(sym))
            enode_store.addDistClass(tr);

        Pterm& tm = term_store[tr];
        for (int i = 0; i < tm.size(); i++) {
            if (logic.isIte(term_store[tm[i]].symb())) {
                // (1) Add a new term o_ite with no arguments and same sort as tm[i]
                // (2) add tm[i] to ites
                // (3) replace tm[i] with o_ite
                SRef sr = sym_store[term_store[tm[i]].symb()].rsort();
                vec<SRef> sort_args;
                sort_args.push(sr);
                char* name = NULL;
                asprintf(&name, ".oite%d", tm[i].x);
                SymRef sym = sym_store.newSymb(name, sort_args);
                // The symbol might already be there
                if (sym == SymRef_Undef) {
                    assert(sym_store.nameToRef(name).size() == 1);
                    sym = sym_store.nameToRef(name)[0];
                }
                PTRef o_ite = term_store.insertTerm(sym, vec<PTRef>());
                assert(o_ite != PTRef_Undef);
                // The old term goes to PtPair
                ites.push(PtPair(tm[i], o_ite));
#ifdef PEDANTIC_DEBUG
                cerr << "Added the term " << term_store.printTerm(tm[i], true) << " to later processing" << endl;
                cerr << "; changing " << term_store.printTerm(tr) << " to ";
#endif
                tm[i] = o_ite;
#ifdef PEDANTIC_DEBUG
                cerr << term_store.printTerm(tr) << endl;
#endif
            }
            queue.push(PtChild(tm[i], tr, i));
        }
    }

#ifdef PEDANTIC_DEBUG
    bool new_terms = false;
#endif

    // construct an enode term for each term in to_process
    // Normalize the terms so that there will be no two UF terms with the
    // same name.
    for (int i = to_process.size() - 1; i >= 0; i--) {
        PtChild& child = to_process[i];
        PTRef tr = child.tr;
        PTRef parent = child.parent;
        int child_pos = child.pos;
#ifdef PEDANTIC_DEBUG
        if (parent != PTRef_Undef)
            cerr << "Now constructing / normalizing term " << term_store.printTerm(tr, true)
                 << " which is child nr " << child_pos << " of " << term_store.printTerm(parent, true) << endl;
        else
            cerr << "Now constructing / normalizing term " << term_store.printTerm(tr, true) << endl;

#endif
        if (!enode_store.termToERef.contains(tr)) {
#ifdef PEDANTIC_DEBUG
            new_terms = true;
#endif
            Pterm& tm = term_store[tr];
            if (sym_store[tm.symb()].commutes()) {
#ifdef PEDANTIC_DEBUG
                cerr << "The term " << term_store.printTerm(tr) << " is commutative"
                     << " and will be sorted to ";
#endif
                termSort(tm);
#ifdef PEDANTIC_DEBUG
                cerr << term_store.printTerm(tr) << "." << endl;
#endif
            }
            ERef sym = enode_store.addSymb(tm.symb());
            ERef cdr = ERef_Nil;
            for (int j = tm.size()-1; j >= 0; j--) {
#ifdef PEDANTIC_DEBUG
                assert( checkParents(cdr) );
#endif
                ERef car = enode_store.termToERef[tm[j]];
#ifdef PEDANTIC_DEBUG
                ERef prev_cdr = cdr;
                assert (enode_store[car].getRoot() == car);
                assert (enode_store[cdr].getRoot() == cdr);
#endif
                cdr = enode_store.addList(car, cdr);
#ifdef PEDANTIC_DEBUG
                assert( checkParents( car ) );
                assert( checkParents( prev_cdr ) );
                assert( checkParents( cdr ) );
                assert( checkInvariants( ) );
#endif
            }
            // Canonize the term representation
            rval = enode_store.addTerm(sym, cdr, tr);
            if (rval != tr) {
#ifdef PEDANTIC_DEBUG
                cout << "Duplicate: " << term_store.printTerm(rval)
                     << " equals " << term_store.printTerm(tr) << endl;
                ERef tr_new = enode_store.termToERef[rval];
                assert( checkParents( tr_new ) );
                assert( checkInvariants( ) );
#endif
                // Fix the parent term to point to the canonical
                // representative of the child term.
                if (child.parent != PTRef_Undef)
                    term_store[child.parent][child_pos] = rval;
            }
        }
        else {
            // Canonize
            // TODO: It would be better to use a special mapping from TRefs to canon TRefs
            ERef tmp = enode_store.termToERef[tr];
            rval = enode_store.ERefToTerms[tmp][0];
            if (child.parent != PTRef_Undef)
                term_store[child.parent][child_pos] = rval;
#ifdef PEDANTIC_DEBUG
            if (rval != tr)
                cerr << "Canonized " << term_store.printTerm(child.parent, true);
#endif
        }
    }

#ifdef PEDANTIC_DEBUG
//    if (not new_terms)
//        cout << "All was seen" << endl;
#endif

    // Check if this term already exists
    Pterm& t = term_store[term];
    vec<ERef> canon_args;
    for (int i = 0; i < t.size(); i++)
        canon_args.push(enode_store.termToERef[t[i]]);
    if (sym_store[t.symb()].commutes())
        sort(canon_args);

    if (logic.isEquality(t.symb())) {
        PTRef val = PTRef_Undef;
        if (eq_terms.peek(canon_args, val))
            return val;
        else
            eq_terms.insert(canon_args, term);
    }
    else if (logic.isDisequality(term_store[term].symb())) {
        PTRef val = PTRef_Undef;
        if (deq_terms.peek(canon_args, val))
            return val;
        else
            deq_terms.insert(canon_args, term);
    }
    else if (logic.isUP(term)) {
        PTRef val = PTRef_Undef;
        // Here we need to consider also the symbol
        canon_args.push(enode_store.symToERef[term_store[term].symb()]);
        if (up_terms.peek(canon_args, val))
            return val;
        else
            up_terms.insert(canon_args, term);
    }

    return term;
}


lbool Egraph::addEquality(PTRef term) {
    Pterm& pt = term_store[term];
    assert(pt.size() == 2);

    bool res = true;
    PTRef e = pt[0];
    for (int i = 1; i < pt.size() && res == true; i++)
        res = assertEq(e, pt[i], term);

    return res == false ? l_False : l_Undef;
}

lbool Egraph::addDisequality(PTRef term) {
    Pterm& pt = term_store[term];
    bool res = true;

    if (pt.size() == 2)
        res = assertNEq(pt[0], pt[1], term);
    else
        res = assertDist(term, term);

    return res == false ? l_False : l_Undef;
}

lbool Egraph::addTrue(PTRef term) {
    lbool res = assertEq(term, logic.getTerm_true(), term);
    return res == false ? l_False : l_Undef;
}

lbool Egraph::addFalse(PTRef term) {
    lbool res = assertEq(term, logic.getTerm_false(), term);
    return res == false ? l_False : l_Undef;
}

//===========================================================================
// Private Routines for Core Theory Solver

//
// Assert an equality between nodes x and y
//
bool Egraph::assertEq ( PTRef tr_x, PTRef tr_y, PTRef r )
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

    const bool res = mergeLoop( r );

    return res;
}

//
// Merge what is in pending and propagate to parents
//
bool Egraph::mergeLoop( PTRef reason )
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

        if ( en_p.isTerm( ) )
            expStoreExplanation( p, q, congruence_pending ? PTRef_Undef : reason );

        // Check if they can't be merged
        PTRef reason_inequality;
        bool res = unmergeable( en_p.getRoot(), en_q.getRoot(), reason_inequality );

        // They are not unmergable, so they can be merged
        if ( !res ) {

            merge( en_p.getRoot( ), en_q.getRoot( ) );
            congruence_pending = true;
            continue;
        }

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

        if ( reason_inequality == PTRef_Undef ) {
            assert(false);
            Enode& en_proot = enode_store[enr_proot];
            Enode& en_qroot = enode_store[enr_qroot];

            assert( sym_store[term_store[en_proot.getTerm()].symb()].isConstant() );
            assert( sym_store[term_store[en_qroot.getTerm()].symb()].isConstant() );

            assert( en_proot.getTerm() != en_qroot.getTerm() );
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
            exp_pending.push( en_p.getTerm() );
            exp_pending.push( en_proot.getTerm() );
            // 2. why q and q->constant are equal
            exp_pending.push( en_q.getTerm() );
            exp_pending.push( en_qroot.getTerm() );
            // 3. why p and q are equal
            exp_pending.push( en_q.getTerm() );
            exp_pending.push( en_p.getTerm() );

            initDup1( );
            expExplain( );
            doneDup1( );
        }
        // Does the reason term correspond to disequality symbol
        else if ( logic.isDisequality(term_store[reason_inequality].symb()) ) {
            // The reason is a distinction, but skip the false equality
            if (reason_inequality != Eq_FALSE)
                explanation.push( reason_inequality );
            // We should iterate through the elements
            // of the distinction and find which atoms
            // are causing the conflict
            Pterm& pt_reason = term_store[reason_inequality];
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
#ifdef PRODUCE_PROOF
            expExplain( reason_1, reason_2, reason_inequality );
#else
            expExplain( reason_1, reason_2 );
#endif
        }
        else if ( logic.isEquality(term_store[reason_inequality].symb()) ) {
            // The reason is a negated equality
            Pterm& pt_reason = term_store[reason_inequality];

            // Hmm, the difference being?
//          if ( config.incremental ) {
//              Enode * s = reason;
//              explanation.push_back( s );
//          }
//          else
//              explanation.push_back( reason );

            if (reason_inequality != Eq_FALSE)
                explanation.push(reason_inequality);

            // The equality
            // If properly booleanized, the left and righ sides of equality
            // will always be UF terms
            // The left hand side of the equality
            reason_1 = pt_reason[0];
            // The rhs of the equality
            reason_2 = pt_reason[1];
//          reason_1 = enode_store.termToERef[pt_reason[0]];
//          reason_2 = enode_store.termToERef[pt_reason[1]];

            assert( reason_1 != PTRef_Undef );
            assert( reason_2 != PTRef_Undef );

//#if VERBOSE
#ifdef PEDANTIC_DEBUG
            cerr << "Reason is neg equality: " << term_store.printTerm(reason_inequality) << endl;
#endif
//#endif
#ifdef PRODUCE_PROOF
            expExplain( reason_1, reason_2, reason_inequality );
#else
            expExplain( reason_1, reason_2 );
#endif
        }
        else if ( logic.isUP(reason_inequality) ) {
            // The reason is an uninterpreted predicate
            assert(false);
            if (reason_inequality != Eq_FALSE)
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
bool Egraph::assertNEq ( PTRef x, PTRef y, PTRef r )
{
    checkFaGarbage();
#if MORE_DEDUCTIONS
    neq_list.push_back( r );
    undo_stack_oper.push_back( ASSERT_NEQ );
    undo_stack_term.push_back( r );
#endif

    ERef p = enode_store[enode_store.termToERef[x]].getRoot();
    ERef q = enode_store[enode_store.termToERef[y]].getRoot();

    // They can't be different if the nodes are in the same class
    if ( p == q ) {
        if (r != Eq_FALSE) explanation.push( r );
#ifdef PRODUCE_PROOF
        expExplain( x, y, r );
#else
        expExplain( x, y );
#endif

#ifdef PEDANTIC_DEBUG
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
    ELRef pdist = forbid_allocator.alloc(p, r);
    Enode& en_q = enode_store[q];
    // If there is no node in forbid list
    if ( en_q.getForbid() == ELRef_Undef ) {
        en_q.setForbid( pdist );
        forbid_allocator[pdist].link = pdist;
    }
    // Otherwise we should put the new node after the first
    // and make the first point to pdist. This is because
    // the list is circular, but could be emptq. Therefore
    // we need a "reference" element for keeping it circular.
    // So the last insertion is either the second element or
    // the only present in the list
    else {
        forbid_allocator[pdist].link = forbid_allocator[en_q.getForbid()].link;
        forbid_allocator[en_q.getForbid()].link = pdist;
    }

    // Create new distinction in p
    ELRef qdist = forbid_allocator.alloc(q, r);
    Enode& en_p = enode_store[p];
    if ( en_p.getForbid() == ELRef_Undef ) {
        en_p.setForbid( qdist );
        forbid_allocator[qdist].link = qdist;
    }
    // Same arguments above
    else {
        Elist& forb_p = forbid_allocator[en_p.getForbid()];
        forbid_allocator[qdist].link = forb_p.link;
        forb_p.link = qdist;
    }

    // Save operation in undo_stack
    undo_stack_main.push( Undo(DISEQ, q) );

    return true;
}

// Assert a distinction on arguments of tr_d

bool Egraph::assertDist( PTRef tr_d, PTRef tr_r )
{
    assert(tr_d == tr_r);

    // Retrieve distinction number
    size_t index = enode_store.getDistIndex(tr_d);
    // While asserting, check that no two nodes are congruent
    Map< enodeid_t, ERef, EnodeIdHash, Equal<enodeid_t> > root_to_enode;
    // Nodes changed
    vec<ERef> nodes_changed;
    // Assign distinction flag to all arguments
    Pterm& pt_d = term_store[tr_d];
    for (int i = 0; i < pt_d.size(); i++) {
        PTRef tr_c = pt_d[i];
        ERef er_c = enode_store.termToERef[tr_c];
        Enode& en_c = enode_store[er_c];
        assert(en_c.isTerm());

        enodeid_t root_id = enode_store[en_c.getRoot()].getCid();
        if ( root_to_enode.contains(root_id) ) {
            // Two equivalent nodes in the same distinction. Conflict
            if (tr_r != Eq_FALSE)
                explanation.push(tr_r);
            // Extract the other node with the same root
            ERef p = root_to_enode[root_id];
            // Check condition
            assert( enode_store[p].getRoot() == en_c.getRoot() );
            // Retrieve explanation
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
        Enode& root = enode_store[en_c.getRoot()];
        root.setDistClasses( (root.getDistClasses( ) | SETBIT( index )) );
        nodes_changed.push(en_c.getRoot());
    }
    // Distinction pushed without conflict
    undo_stack_main.push(Undo(DIST, tr_d));
    return true;
}

void Egraph::undoDistinction(PTRef tr_d) {
    dist_t index = enode_store.getDistIndex(tr_d);
    Pterm& pt_d = term_store[tr_d];
    for (int i = 0; i < pt_d.size(); i++) {
        PTRef tr_c = pt_d[i];
        ERef er_c = enode_store.termToERef[tr_c];
        Enode& en_c = enode_store[er_c];
        assert(en_c.isTerm());
        en_c.setDistClasses( en_c.getDistClasses() & ~(SETBIT(index)) );
    }
#ifdef PEDANTIC_DEBUG
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
void Egraph::merge ( ERef x, ERef y )
{
#ifdef PEDANTIC_DEBUG
//    cerr << "Asserting equality of the following enodes: " << endl
//         << enode_store.printEnode(x) << endl
//         << enode_store.printEnode(y) << endl;
    assert( checkParents( x ) );
    assert( checkParents( y ) );
    assert( checkInvariants( ) );
#endif

    // This is weird.  If I get the references here and change them afterwards, the cgdata will not be correct.
//    Enode& en_x = enode_store[x];
//    Enode& en_y = enode_store[y];

//    assert( !en_x.isConstant( ) || !en_y.isConstant( ) );
//    assert( !en_x.isConstant( ) || en_x.getSize( ) == 1 );
//    assert( !y->isConstant( ) || y->getSize( ) == 1 );
    assert( enode_store[x].getRoot( ) != enode_store[y].getRoot( ) );
    assert( x == enode_store[x].getRoot( ) );
    assert( y == enode_store[y].getRoot( ) );

  // Swap x,y if y has a larger eq class
    if ( enode_store[x].getSize( ) < enode_store[y].getSize( ) )
//    || en_x.isConstant( ) )
    {
        ERef tmp = x;
        x = y;
        y = tmp;
    }
        // Get the references right here
    Enode& en_x = enode_store[x];
    Enode& en_y = enode_store[y];

    assert(en_x.type() == en_y.type());
//    assert( !x->isConstant( ) );

  // TODO:
  // Propagate equalities to other ordinary theories
  //

  // Update forbid list for x by adding elements of y
    if ( en_y.getForbid( ) != ELRef_Undef ) {
        // We assign the same forbid list
        if ( en_x.getForbid( ) == ELRef_Undef )
            en_x.setForbid( en_y.getForbid( ) );
        // Otherwise we splice the two lists
        else {
            ELRef tmp = forbid_allocator[en_x.getForbid()].link;
            forbid_allocator[en_x.getForbid()].link = forbid_allocator[en_y.getForbid()].link;
            forbid_allocator[en_y.getForbid()].link = tmp;
        }
    }

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
//        deduce( x, y );
    }

    // Perform the union of the two equivalence classes
    // i.e. reroot every node in y's class to point to x

    ERef v = y;
    const ERef vstart = v;
    while (true) {
        Enode& en_v = enode_store[v];
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
#ifdef PEDANTIC_DEBUG
    checkParents(x);
#endif
    // Store info about the constant
//    if ( en_y.getConstant( ) != E) {
//        assert( en_x.getConstant( ) == NULL );
//        x->setConstant( y->getConstant( ) );
//  }
  // Store info about the constant
//  else if ( x->getConstant( ) != NULL )
//  {
//    assert( y->getConstant( ) == NULL );
//    y->setConstant( x->getConstant( ) );
//  }

  // Push undo record
    undo_stack_main.push( Undo(MERGE,y) );

//    if (en_x.isTerm()) {
//        printf("Merging %s and %s, undo stack size %d\n", term_store.printTerm(en_x.getTerm()), term_store.printTerm(en_y.getTerm()), undo_stack_term.size());
//        printf("There are %d backtrack points\n", backtrack_points.size());
//    }

#ifdef PEDANTIC_DEBUG
    assert( checkParents( x ) );
    assert( checkParents( y ) );
    assert( checkInvariants( ) );
#endif
}

//
// Deduce facts from the merge of x and y
//
//void Egraph::deduce( Enode * x, Enode * y )
//{
//  lbool deduced_polarity = l_Undef;
//
//  if ( x->getConstant( ) == etrue )
//    deduced_polarity = l_True;
//  else if ( x->getConstant( ) == efalse )
//    deduced_polarity = l_False;
//
//  // Let be y store the representant of the class
//  // containing the facts that we are about to deduce
//  if ( deduced_polarity == l_Undef )
//  {
//    Enode * tmp = x;
//    x = y;
//    y = tmp;
//  }
//
//  if ( x->getConstant( ) == etrue )
//    deduced_polarity = l_True;
//  else if ( x->getConstant( ) == efalse )
//    deduced_polarity = l_False;
//
//  if ( deduced_polarity == l_Undef )
//    return;
//
//  Enode * v = y;
//  const Enode * vstart = v;
//  for (;;)
//  {
//    // We deduce only things that aren't currently assigned or
//    // that we previously deduced on this branch
//    Enode * sv = v;
//    if ( !sv->hasPolarity( )
//      && !sv->isDeduced( ) 
//      // Also when incrementality is used, node should be explicitly informed
//      && ( config.incremental == 0 || informed.find( sv->getId( ) ) != informed.end( ) )
//      )
//    {
//      sv->setDeduced( deduced_polarity, id );
//      deductions.push_back( sv );
//#ifdef STATISTICS
//      tsolvers_stats[ 0 ]->deductions_done ++;
//#endif
//    }
//    v = v->getNext( );
//    if ( v == vstart )
//      break;
//  }
//
//#ifdef PEDANTIC_DEBUG
//  assert( checkInvariants( ) );
//#endif
//}

//
// Starts with the E-graph state that existed after the
// pertinent merge and restores the E-graph to the state
// it had before the pertinent merge
//
void Egraph::undoMerge( ERef y )
{
    assert( y != ERef_Undef );

    Enode& en_y = enode_store[y];

    // x is the node that was merged with y
    ERef x = en_y.getRoot( );

    assert( x != ERef_Undef );

    Enode& en_x = enode_store[x];

#if VERBOSE
    cerr << "UM: Undoing merge of " << y << " and " << x << endl;
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
#ifdef PEDANTIC_DEBUG
            if (enode_store.containsSig(p)) {
                cerr << enode_store.printEnode(p);
                assert(false);
            }
#else
            assert(!enode_store.containsSig(p));
#endif
            enode_store.insertSig(p);
            // remove all guests now that the signature has changed
//            if (en_p.isTerm() && enode_store.ERefToTerms[p].size() > 1) {
//                vec<PTRef>& guests = enode_store.ERefToTerms[p];
//                printf("Removing guests from enode %d\n", p.x);
//                for (int i = 1; i < guests.size(); i++) {
//                    enode_store.termToERef.remove(guests[i]);
//                    printf("  %s (%d)\n", term_store.printTerm(guests[i]), guests[i].x);
//                }
//                guests.shrink(guests.size()-1);
//            }
//      (void)res; // Huh?
//            assert( res == p );
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
    if ( en_x.getForbid( ) == en_y.getForbid( ) )
        en_x.setForbid( ELRef_Undef );
    // Unsplice back the two lists
    else if ( en_y.getForbid( ) != ELRef_Undef ) {
        ELRef tmp = forbid_allocator[en_x.getForbid()].link;
        forbid_allocator[en_x.getForbid()].link = forbid_allocator[en_y.getForbid()].link;
        forbid_allocator[en_y.getForbid()].link = tmp;
    }


//    if ( en_y.getConstant() != NULL )
//  {
//    Enode * yc = y->getConstant( );
//    Enode * xc = x->getConstant( );
//    (void)xc;
//    assert( yc == xc );
    // Invariant: the constant comes from one class only
    // No merge can occur beteween terms that point to the
    // same constant, as they would be in the same class already
//    assert( ( yc->getRoot( ) == y && xc->getRoot( ) != x )
//	 || ( yc->getRoot( ) != y && xc->getRoot( ) == x ) );
    // Determine from which class the constant comes from
//    if ( yc->getRoot( ) == y )
//      x->setConstant( NULL );
//    else
//      y->setConstant( NULL );
//  }

  //
  // TODO: unmerge for ordinary theories
  //

#ifdef PEDANTIC_DEBUG
  assert( checkParents( y ) );
  assert( checkParents( x ) );
  assert( checkInvariants( ) );
#endif
}

//
// Restore the state before the addition of a disequality
//
void Egraph::undoDisequality ( ERef x )
{
    Enode& en_x = enode_store[x];
    assert( en_x.getForbid() != ELRef_Undef );

    // We have to distinct two cases:
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
    // Some checks
    assert( yfirst != ELRef_Undef );
    Elist& el_yfirst = forbid_allocator[yfirst];
    assert( el_yfirst.link != yfirst || el_yfirst.e == x );
    assert( el_yfirst.link == yfirst || forbid_allocator[el_yfirst.link].e == x );
    assert( en_x.getRoot( ) != en_y.getRoot( ) );

    ELRef ydist = el_xfirst.link == xfirst ? xfirst : el_xfirst.link;
    Elist& el_ydist = forbid_allocator[ydist];

    // Only one node in the list
    if ( el_ydist.link == ydist )
        en_x.setForbid( ELRef_Undef );
    // Other nodes in the list
    else
        el_xfirst.link = el_ydist.link;
    forbid_allocator.free(ydist);

    ELRef xdist = el_yfirst.link == yfirst ? yfirst : el_yfirst.link;
    Elist& el_xdist = forbid_allocator[xdist];

    // Only one node in the list
    if ( el_xdist.link == xdist )
    en_y.setForbid( ELRef_Undef );
    // Other nodes in the list
    else
        el_yfirst.link = el_xdist.link;
    forbid_allocator.free(xdist);

#ifdef PEDANTIC_DEBUG
    assert( checkInvariants( ) );
#endif
}

bool Egraph::unmergeable (ERef x, ERef y, PTRef& r)
{
    assert( x != ERef_Undef );
    assert( y != ERef_Undef );

    ERef p = enode_store[x].getRoot();
    ERef q = enode_store[y].getRoot();
    // If they are in the same class, they can merge
    if ( p == q ) return false;
    // Check if they have different constants. It is sufficient
    // to check that they both have a constant. It is not
    // possible that the constant is the same. In fact if it was
    // the same, they would be in the same class, but they are not

//  if ( p->getConstant( ) != NULL && q->getConstant( ) != NULL ) return true;
    // Check if they are part of the same distinction (general distinction)
    Enode& en_p = enode_store[p];
    Enode& en_q = enode_store[q];
    dist_t intersection = ( en_p.getDistClasses( ) & en_q.getDistClasses( ) );

    if ( intersection ) {
        // Compute the first index in the intersection
        // TODO: Use hacker's delight
        unsigned index = 0;
        while ( ( intersection & 1 ) == 0 ) {
            intersection = intersection >> 1;
            index ++;
        }
        r = enode_store.getDistTerm(index);
        assert( r != PTRef_Undef );
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

    r = PTRef_Undef;

    for (;;) {
        Elist& el_pptr = forbid_allocator[pptr];
        Elist& el_qptr = forbid_allocator[qptr];
        // They are unmergable if they are on the other forbid list
        if ( enode_store[el_pptr.e].getRoot( ) == q ) {
            r = el_pptr.reason;
            return true;
        }
        if ( enode_store[el_qptr.e].getRoot( ) == p ) {
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
    assert( r == PTRef_Undef );
    return false;
}

//
// Creates the dynamic version of the enode
//
//void Egraph::initializeCongInc( Enode * top )
//{
//  assert( top );
//  assert( initialized.find( top->getId( ) ) == initialized.end( ) );
//
//  vector< Enode * > unprocessed_enodes;
//  unprocessed_enodes.push_back( top );
//
//  while ( !unprocessed_enodes.empty( ) )
//  {
//    Enode * e = unprocessed_enodes.back( );
//    assert( e );
//    
//    if ( initialized.find( e->getId( ) ) != initialized.end( ) )
//    {
//      unprocessed_enodes.pop_back( );
//      continue;
//    }
//
//    bool unprocessed_children = false;
//    if ( e->getCar( )->isTerm( ) 
//      && initialized.find( e->getCar( )->getId( ) ) == initialized.end( ) )
//    {
//      unprocessed_enodes.push_back( e->getCar( ) );
//      unprocessed_children = true;
//    }
//    if ( !e->getCdr( )->isEnil( ) 
//      && initialized.find( e->getCdr( )->getId( ) ) == initialized.end( ) )
//    {
//      unprocessed_enodes.push_back( e->getCdr( ) );
//      unprocessed_children = true;
//    }
//
//    if ( unprocessed_children )
//      continue;
//
//    unprocessed_enodes.pop_back( );
//    // 
//    // Initialization happens here
//    //
//    assert( e->isTerm( ) || e->isList( ) );
//    assert( !e->isEnil( ) );
//    assert( !e->isTerm( ) || !e->isTrue( ) );
//    assert( !e->isTerm( ) || !e->isFalse( ) );
//    // If it's safe to initialize
//    if ( e->getCar( ) == e->getCar( )->getRoot( ) 
//      && e->getCdr( ) == e->getCdr( )->getRoot( ) )
//      initializeCong( e );
//    // Otherwise specialized initialization
//    // with fake merges
//    else
//      initializeAndMerge( e );
//  }
//
//  assert( initialized.find( top->getId( ) ) != initialized.end( ) );
//}

//void Egraph::initializeAndMerge( Enode * e )
//{
//#if VERBOSE
//  cerr << endl;
//  cerr << "IM: BEGIN INITIALIZING: " << e << endl;
//#endif
//
//  assert( e->getCar( ) != e->getCar( )->getRoot( )
//       || e->getCdr( ) != e->getCdr( )->getRoot( ) );
//  assert( !e->hasCongData( ) );
//  e->allocCongData( );
//  // Node initialized
//  initialized.insert( e->getId( ) );
//
//  // Now we need to adjust data structures as 
//  // either car != car->root or cdr != cdr->root
//
//  Enode * eq = cons( e->getCar( )->getRoot( )
//                   , e->getCdr( )->getRoot( ) );
//
//  // In any case the two terms must be different
//  assert( eq != e );
//  undo_stack_term.push_back( e );
//  undo_stack_oper.push_back( FAKE_MERGE );
//
//#if VERBOSE
//  cerr << "IM: Term: " << e << " is actually equiv to " << eq << endl;
//#endif
//
//  if ( initialized.insert( eq->getId( ) ).second )
//  {
//    assert( !eq->hasCongData( ) );
//    eq->allocCongData( );
//
//    if ( eq->isList( ) )
//      eq->getCar( )->addParent( eq );
//    eq->getCdr( )->addParent( eq );
//
//    undo_stack_term.push_back( eq );
//    undo_stack_oper.push_back( FAKE_INSERT );
//    // Now we need to adjust the signature table
//    // it is possible that the signature of eq is
//    // already used
//    Enode * prev = lookupSigTab( eq );
//    assert( prev != eq );
//    assert( prev == NULL || prev == prev->getCgPtr( ) );
//
//    // Just insert if signature was not there
//    if ( prev == NULL )
//      insertSigTab( eq );
//    // Otherwise prev is the congruence root. This m
//    // eans that eq will not be stored inside sig_tab
//    // However we need to equate the two, as it
//    // is done in normal merge procedure
//    else
//    {
//      // Set congruence pointer to maintain
//      // invariant of signature table
//      eq->setCgPtr( prev );
//      // Add to pending
//      pending.push_back( eq );
//      pending.push_back( prev );
//      // Merge
//      const bool res = mergeLoop( NULL );
//      if ( !res )
//	opensmt_error( "unexpected result" );
//    }
//  }
//#if VERBOSE
//  else
//    cerr << "IM: No need to add: " << eq << endl;
//#endif
//
//#ifdef PEDANTIC_DEBUG
//  assert( !e->isList( ) 
//       || checkParents( e->getCar( ) ) );
//  assert( e->getCdr( )->isEnil( ) 
//       || checkParents( e->getCdr( ) ) );
//#endif
//
//  // Now we need to merge x and eq, since they are equivalent
//  pending.push_back( e );
//  pending.push_back( eq );
//  const bool res = mergeLoop( NULL );
//  if ( !res )
//    opensmt_error( "unexpected result" );
//
//#ifdef PEDANTIC_DEBUG
//  assert( checkParents( e ) );
//  assert( checkParents( eq ) );
//  assert( checkInvariants( ) );
//#endif
//
//#if VERBOSE
//  cerr << "IM: END INITIALING: " << e << endl;
//#endif
//}

//
// Creates a new enode modulo equivalence
//
//Enode * Egraph::uCons( Enode * car, Enode * cdr )
//{
//  assert( false );
//  assert( config.incremental );
//  assert( !config.uf_disable );
//  assert( car );
//  assert( cdr );
//  assert( car->isTerm( ) || car->isSymb( ) || car->isNumb( ) );
//  assert( cdr->isList( ) );
//  // Move to roots
//  car = car->getRoot( );
//  cdr = cdr->getRoot( );
//  Enode * e = NULL;
//  // Create and insert a new enode if necessary
//  e = insertSigTab( id_to_enode.size( ), car, cdr );
//  assert( e );
//  // The node was there already. Return it
//  if ( (enodeid_t)id_to_enode.size( ) != e->getId( ) )
//    return e;
//  assert( e->getCar( ) == e->getCar( )->getRoot( ) );
//  assert( e->getCdr( ) == e->getCdr( )->getRoot( ) );
//  // We keep the created enode
//  id_to_enode.push_back( e );
//  // Initialize its congruence data structures
//  assert( initialized.find( e->getId( ) ) == initialized.end( ) );
//  assert( !e->hasCongData( ) );
//  e->allocCongData( );
//  // Set constant for constants
//  if ( e->isConstant( ) )
//    e->setConstant( e );
//  // Add parents relationships
//  if ( e->isList( ) )
//    e->getCar( )->addParent( e );
//  e->getCdr( )->addParent( e );
//  // Node initialized
//  initialized.insert( e->getId( ) );
//  // Insert in SigTab
//  insertSigTab( e );
//  // Save backtrack info
//  undo_stack_term.push_back( e );
//  undo_stack_oper.push_back( CONS );
//  assert( undo_stack_oper.size( ) == undo_stack_term.size( ) );
//  return e;
//}


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

//=================================================================================================
// Garbage Collection methods:

void Egraph::relocAll(ELAllocator& to) {
    for (int i = 0; i < enode_store.enodes.size(); i++) {
        ERef er = enode_store.enodes[i];
        Enode& en = enode_store[er];
        assert(en.isTerm());

#ifdef PEDANTIC_DEBUG
        cerr << enode_store.printEnode(er);
#endif
        const ELRef start = en.getForbid();
        ELRef& start_ref = en.altForbid();
        bool done = false;
        ELRef& curr_ch = start_ref;
        if (curr_ch == ELRef_Undef) continue;
        ELRef curr_fx = start_ref;
        ELRef prev_fx = ELRef_Undef;
        while (true) {
            forbid_allocator.reloc(curr_ch, to);
            if (prev_fx != ELRef_Undef)
                to[prev_fx].link = curr_ch;
            // curr now points to "to"
            if (done == true) break;
            prev_fx = curr_ch;
            curr_ch = forbid_allocator[curr_fx].link;
            curr_fx = forbid_allocator[curr_fx].link;
            if (curr_fx == start) done = true;
        }
    }
}

void Egraph::faGarbageCollect() {
    ELAllocator to(forbid_allocator.size() - forbid_allocator.wasted());

    relocAll(to);
    if (config.verbosity() >= 2)
        printf("Garbage collection:   %12d bytes => %12d bytes|\n",
               forbid_allocator.size()*ELAllocator::Unit_Size, to.size()*ELAllocator::Unit_Size);
    to.moveTo(forbid_allocator);
}
