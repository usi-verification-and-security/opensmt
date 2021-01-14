/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2016 Antti Hyvarinen
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

#include "THandler.h"
#include "CoreSMTSolver.h"
#include "TSolver.h"
#include "ModelBuilder.h"

#include <sys/wait.h>
#include <assert.h>

void THandler::backtrack(int lev)
{
    unsigned int backTrackPointsCounter = 0;
    // Undoes the state of theory atoms if needed
    while ( (int)stack.size( ) > (lev > 0 ? lev : 0) ) {
        PTRef e = stack.last();
        stack.pop();

        // It was var_True or var_False
        if (e == getLogic().getTerm_true() || e == getLogic().getTerm_false()) continue;

        if (!getLogic().isTheoryTerm(e)) continue;
        ++backTrackPointsCounter;
    }
    for (int i = 0; i < getSolverHandler().tsolvers.size(); i++) {
        if (getSolverHandler().tsolvers[i] != nullptr)
            getSolverHandler().tsolvers[i]->popBacktrackPoints(backTrackPointsCounter);
    }

    checked_trail_size = stack.size( );
}

// Push newly found literals from trail to the solvers
bool THandler::assertLits(const vec<Lit> & trail)
{
    bool res = true;

    assert( checked_trail_size == stack.size_( ) );
    assert( (int)stack.size( ) <= trail.size( ) );

#ifdef PEDANTIC_DEBUG
    vec<Lit> assertions;
#endif

    for ( int i = checked_trail_size;
          i < trail.size( ) && (res != false);
          i ++ ) {
        const Lit l = trail[ i ];
        const Var v = var( l );

        PTRef pt_r = tmap.varToPTRef(v);
        stack.push( pt_r );
        if (!getLogic().isTheoryTerm(pt_r)) continue;
        assert(getLogic().isTheoryTerm(pt_r));


        if ( pt_r == getLogic().getTerm_true() )       { assert(sign(l) == false); continue; }
        else if ( pt_r == getLogic().getTerm_false() ) { assert(sign(l) == true ); continue; }

#ifdef VERBOSE_EUF
        // We are interested only in theory atoms from here onwards
        cerr << "Asserting " << (sign(l) ? "not " : "")  << getLogic().printTerm(pt_r) << endl;
//        cerr << "Asserting " << (sign(l) ? "not " : "")  << getLogic().printTerm(pt_r) << " (" << pt_r.x << ")" << endl;

//        cout << printAssertion(l);
#endif

        res = assertLit(PtAsgn(pt_r, sign(l) ? l_False : l_True));
//        res &= check(true);

#ifdef VERBOSE_EUF
//        if (res == l_False) {
//            cerr << "conflict asserting " << logic.term_store.printTerm(pt_r)
//                 << endl;
//        }
#endif
//    if ( !res && config.certification_level > 2 )
//      verifyCallWithExternalTool( res, i );
    }

    checked_trail_size = stack.size( );
//  assert( !res || trail.size( ) == (int)stack.size( ) );

    return res;
}


// Check the assignment with equality solver
TRes THandler::check(bool complete) {
    return getSolverHandler().check(complete);
//  if ( complete && config.certification_level > 2 )
//    verifyCallWithExternalTool( res, trail.size( ) - 1 );
}

void THandler::getNewSplits(vec<Lit> &splits) {
    vec<PTRef> split_terms;
    for (int i = 0; i < getSolverHandler().tsolvers.size(); i++) {
        if (getSolverHandler().tsolvers[i] != nullptr && getSolverHandler().tsolvers[i]->hasNewSplits()) {
            getSolverHandler().tsolvers[i]->getNewSplits(split_terms);
            break;
        }
    }

    if ( split_terms.size() == 0 ) {
        return;
    }

    assert(split_terms.size() == 1);
    PTRef tr = split_terms[0];
    split_terms.pop();
    Logic & logic = getLogic();
    assert(logic.isOr(tr));
    for (int i = 0; i < logic.getPterm(tr).size(); i++) {
        PTRef arg = logic.getPterm(tr)[i];
        Lit l = tmap.getOrCreateLit(arg);
        assert(getLogic().isAtom(arg)); // MB: Needs to be an atom, otherwise the declaration would not work.
        declareAtom(arg);
        informNewSplit(arg);
        splits.push(l);
    }
}

//
// Return the conflict generated by a theory solver
//
void THandler::getConflict (
        vec<Lit> & conflict
        , vec<VarData>& vardata
        , int & max_decision_level
    )
{
    // First of all, the explanation in a tsolver is
    // stored as conjunction of enodes e1,...,en
    // with associated polarities p1,...,pn. Since the sat-solver
    // wants a clause we store it in the form ( l1 | ... | ln )
    // where li is the literal corresponding with ei with polarity !pi
    vec<PtAsgn> explanation;
    {
        int i;
        for (i = 0; i < getSolverHandler().tsolvers.size(); i++) {
            if (getSolverHandler().tsolvers[i] != nullptr && getSolverHandler().tsolvers[i]->hasExplanation()) {
                getSolverHandler().tsolvers[i]->getConflict(false, explanation);
                break;
            }
        }
        assert(i != getSolverHandler().tsolvers.size());
    }

#ifdef VERBOSE_EUF
//    std::cout << printExplanation(explanation, assigns);
#endif
    if (explanation.size() == 0) {
        max_decision_level = 0;
        return;
    }

    max_decision_level = -1;
    for (int i = 0; i < explanation.size(); ++i) {
        PtAsgn const & ei = explanation[i];
        assert(ei.sgn == l_True || ei.sgn == l_False);
        Var v = ptrefToVar(ei.tr);
        bool negate = ei.sgn == l_False;
        Lit l = mkLit(v, !negate);
        conflict.push(l);

        if (max_decision_level < vardata[v].level) {
            max_decision_level = vardata[v].level;
        }
    }
}


PTRef
THandler::getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels, PartitionManager &pmanager)
{
    return getSolverHandler().getInterpolant(mask, labels, pmanager);
}

//
// It is in principle possible that the egraph contains deduceable literals
// that the SAT solver is not aware of because they have been simplified due to
// appearing only in clauses that are tautological.  We check this here, but it
// would be better to remove them from egraph after simplifications are done.
//
Lit THandler::getDeduction() {
    PtAsgn_reason e = PtAsgn_reason_Undef;
    while (true) {
        for (int i = 0; i < getSolverHandler().tsolvers.size(); i++) {
            if (getSolverHandler().tsolvers[i] != NULL) e = getSolverHandler().tsolvers[i]->getDeduction();
            if (e.tr != PTRef_Undef) break;
        }
        if ( e.tr == PTRef_Undef ) {
            return lit_Undef;
        }
        //assert(e.reason != PTRef_Undef);
        //assert(e.sgn != l_Undef);
#ifdef PEDANTIC_DEBUG
        if (!tmap.hasLit(e.tr))
            cerr << "Missing (optimized) deduced literal ignored: " << getLogic().printTerm(e.tr) << endl;
#endif
        if (!tmap.hasLit(e.tr)) continue;
        break;
    }
    return e.sgn == l_True ? tmap.getLit(e.tr) : ~tmap.getLit(e.tr);

//  if ( config.certification_level > 1 )
//    verifyDeductionWithExternalTool( e );

//  assert( e->isDeduced( ) );
//  assert( e->getDeduced( ) == l_False
//       || e->getDeduced( ) == l_True );
//  bool negate = e->getDeduced( ) == l_False;
//  Var v = enodeToVar( e );
//  return Lit( v, negate );

}

Lit THandler::getSuggestion( ) {
    PTRef e = PTRef_Undef; // egraph.getSuggestion( );

    if ( e == PTRef_Undef )
        return lit_Undef;

//  bool negate = e->getDecPolarity( ) == l_False;
//  Var v = enodeToVar( e );
//  return Lit( v, negate );
    
    return tmap.getLit(e);
}

void THandler::getReason( Lit l, vec< Lit > & reason)
{
    Var   v = var(l);
    PTRef e = tmap.varToPTRef(v);

    // It must be a TAtom and already deduced
    assert(getLogic().isTheoryTerm(e));
    TSolver* solver = getSolverHandler().getReasoningSolverFor(e);
    assert(solver);
    solver->pushBacktrackPoint();
    // Assign temporarily opposite polarity
    PtAsgn conflictingPolarity = PtAsgn(e, sign(~l) ? l_False : l_True);
    lbool res = solver->assertLit(conflictingPolarity) == false ? l_False : l_Undef;

    if ( res != l_False ) {
        std::cout << std::endl << "unknown" << std::endl;
        assert(false);
    }

    // Get Explanation
    vec<PtAsgn> explanation;
    solver->getConflict( true, explanation );
    assert(explanation.size() > 0);

    // Reserve room for implied lit
    reason.push( lit_Undef );
    // Copy explanation

    while ( explanation.size() > 0 ) {
        PtAsgn pa = explanation.last();
        PTRef ei  = pa.tr;
        explanation.pop();

        // Toggle polarity for deduced literal
        if ( e == ei ) {
            // The deduced literal must have been pushed
            // with the the same polarity that has been deduced
            assert((pa.sgn == l_True && sign(l)) || (pa.sgn == l_False && !sign(l))); // The literal is true (sign false) iff the egraph term polarity is false
            reason[0] = l;
        }
        else {
            assert(pa.sgn != l_Undef);
            reason.push(pa.sgn == l_True ? ~tmap.getLit(ei) : tmap.getLit(ei)); // Swap the sign for others
        }
    }
    solver->popBacktrackPoint();

}

#ifdef PEDANTIC_DEBUG

bool THandler::isOnTrail( Lit l, vec<Lit>& trail ) {
    for ( int i = 0 ; i < trail.size( ) ; i ++ )
        if ( trail[ i ] == l ) return true;

    return false;
}

#endif


void
THandler::dumpFormulaToFile( ostream & dump_out, PTRef formula, bool negate )
{
	vector< PTRef > unprocessed_enodes;
	map< PTRef, string > enode_to_def;
	unsigned num_lets = 0;
    Logic& logic = getLogic();

	unprocessed_enodes.push_back( formula );
	// Open assert
	dump_out << "(assert" << endl;
	//
	// Visit the DAG of the formula from the leaves to the root
	//
	while( !unprocessed_enodes.empty( ) )
	{
		PTRef e = unprocessed_enodes.back( );
		//
		// Skip if the node has already been processed before
		//
		if ( enode_to_def.find( e ) != enode_to_def.end( ) )
		{
			unprocessed_enodes.pop_back( );
			continue;
		}

		bool unprocessed_children = false;
        Pterm& term = logic.getPterm(e);
        for(int i = 0; i < term.size(); ++i)
        {
            PTRef pref = term[i];
            //assert(isTerm(pref));
			//
			// Push only if it is unprocessed
			//
			if ( enode_to_def.find( pref ) == enode_to_def.end( ) && (logic.isBooleanOperator( pref ) || logic.isEquality(pref)))
			{
				unprocessed_enodes.push_back( pref );
				unprocessed_children = true;
			}
		}
		//
		// SKip if unprocessed_children
		//
		if ( unprocessed_children ) continue;

		unprocessed_enodes.pop_back( );

		char buf[ 32 ];
		sprintf( buf, "?def%d", Idx(logic.getPterm(e).getId()) );

		// Open let
		dump_out << "(let ";
		// Open binding
		dump_out << "((" << buf << " ";

		if (term.size() > 0 ) dump_out << "(";
		dump_out << logic.printSym(term.symb());
        for(int i = 0; i < term.size(); ++i)
		{
            PTRef pref = term[i];
			if ( logic.isBooleanOperator(pref) || logic.isEquality(pref) )
				dump_out << " " << enode_to_def[ pref ];
			else
			{
				dump_out << " " << logic.printTerm(pref);
				if ( logic.isAnd(e) ) dump_out << endl;
			}
		}
		if ( term.size() > 0 ) dump_out << ")";

		// Closes binding
		dump_out << "))" << endl;
		// Keep track of number of lets to close
		num_lets++;

		assert( enode_to_def.find( e ) == enode_to_def.end( ) );
		enode_to_def[ e ] = buf;
	}
	dump_out << endl;
	// Formula
	if ( negate ) dump_out << "(not ";
	dump_out << enode_to_def[ formula ] << endl;
	if ( negate ) dump_out << ")";
	// Close all lets
	for( unsigned n=1; n <= num_lets; n++ ) dump_out << ")";
	// Closes assert
	dump_out << ")" << endl;
}

void
THandler::dumpHeaderToFile(ostream& dump_out)
{
    Logic& logic = getLogic();
    dump_out << "(set-logic QF_UF)" << endl;

    /*
	dump_out << "(set-info :source |" << endl
			<< "Dumped with "
			<< PACKAGE_STRING
			<< " on "
			<< __DATE__ << "." << endl
			<< "|)"
			<< endl;
	dump_out << "(set-info :smt-lib-version 2.0)" << endl;
    */

    logic.dumpHeaderToFile(dump_out);
}

char* THandler::printAsrtClause(vec<Lit>& r) {
    stringstream os;
    for (int i = 0; i < r.size(); i++) {
        Var v = var(r[i]);
        bool sgn = sign(r[i]);
        os << (sgn ? "not " : "") << getLogic().printTerm(tmap.varToPTRef(v)) << " ";
    }
    return strdup(os.str().c_str());
}

char* THandler::printAsrtClause(Clause* c) {
    vec<Lit> v;
    for (unsigned i = 0; i < c->size(); i++)
        v.push((*c)[i]);
    return printAsrtClause(v);
}

bool THandler::checkTrailConsistency(vec<Lit>& trail) {
    assert(trail.size() >= stack.size()); // There might be extra stuff
                                          // because of conflicting assignments
    for (int i = 0; i < stack.size(); i++) {
        assert(var(trail[i]) == var(tmap.getLit(stack[i])));
//        ||
//               (stack[i] == logic.getTerm_false() &&
//                trail[i] == ~tmap.getLit(stack[i])));
    }
    return true;
}

#ifdef PEDANTIC_DEBUG
std::string THandler::printAssertion(Lit assertion) {
    stringstream os;
    os << "; assertions ";
    Var v = var(assertion);
    PTRef pt_r = tmap.varToPTRef(v);
    if (sign(assertion))
        os << "!";
    os << getLogic().term_store.printTerm(pt_r, true) << "[var " << v << "] " << endl;
    return os.str();
}

//std::string THandler::printExplanation(vec<PtAsgn>& explanation, vec<char>& assigns) {
//    stringstream os;
//    os << "; Conflict: ";
//    for ( int i = 0 ; i < explanation.size( ) ; i ++ ) {
//        if ( i > 0 )
//            os << ", ";
//        Var v = tmap.getVar(explanation[i].tr);
//        lbool val = toLbool(assigns[v]);
//        assert(val != l_Undef);
//        if ( val == l_False )
//            os << "!";
//
//        os << getLogic().term_store.printTerm(explanation[i].tr);
//        os << "[var " << v << "]";
//    }
//    os << endl;
//    return os.str();
//}
#endif

void THandler::clear() { getSolverHandler().clearSolver(); }  // Clear the solvers from their states

Theory& THandler::getTheory() { return theory; }
Logic&  THandler::getLogic()  { return theory.getLogic(); }

TSolverHandler&       THandler::getSolverHandler()       { return theory.getTSolverHandler(); }
const TSolverHandler& THandler::getSolverHandler() const { return theory.getTSolverHandler(); }
TermMapper&           THandler::getTMap()                { return tmap; }

ValPair THandler::getValue          (PTRef tr) const { return getSolverHandler().getValue(tr); };
void    THandler::fillTheoryVars(ModelBuilder &modelBuilder) const { getSolverHandler().fillTheoryVars(modelBuilder); }
void    THandler::addSubstitutions(ModelBuilder &modelBuilder) const { modelBuilder.processSubstitutions(getSolverHandler().substs); }

bool    THandler::isTheoryTerm       ( Var v )       { return getLogic().isTheoryTerm(varToTerm(v)); }
PTRef   THandler::varToTerm          ( Var v ) const { return tmap.varToPTRef(v); }  // Return the term ref corresponding to a variable
Pterm&  THandler::varToPterm         ( Var v)        { return getLogic().getPterm(tmap.varToPTRef(v)); } // Return the term corresponding to a variable
Lit     THandler::PTRefToLit         ( PTRef tr)     { return tmap.getLit(tr); }

void    THandler::getVarName         ( Var v, char** name ) { *name = getLogic().printTerm(tmap.varToPTRef(v)); }

Var     THandler::ptrefToVar         ( PTRef r ) { return tmap.getVar(r); }

void    THandler::computeModel      () { getSolverHandler().computeModel(); } // Computes a model in the solver if necessary
void    THandler::clearModel        () { /*getSolverHandler().clearModel();*/ }   // Clear the model if necessary

bool    THandler::assertLit         (PtAsgn pta) { return getSolverHandler().assertLit(pta); } // Push the assignment to all theory solvers
void    THandler::informNewSplit    (PTRef tr) { getSolverHandler().informNewSplit(tr);  } // The splitting variable might need data structure changes in the solver (e.g. LIA needs to re-build bounds)

PTRef THandler::getSubstitution(PTRef tr) const {
    auto const & subst = getSolverHandler().substs;
    if (subst.has(tr)){
        PtAsgn subs = subst[tr];
        return subs.sgn == l_True ? subs.tr : PTRef_Undef;
    }
    return PTRef_Undef;
}

inline double THandler::drand(double& seed)
{
    seed *= 1389796;
    int q = (int)(seed / 2147483647);
    seed -= (double)q * 2147483647;
    return seed / 2147483647;
}

// Returns a random integer 0 <= x < size. Seed must never be 0.
inline int THandler::irand(double& seed, int size)
{
    return (int)(drand(seed) * size);
}

inline lbool THandler::value (Lit p, vec<lbool>& assigns) const { return assigns[var(p)] ^ sign(p); }