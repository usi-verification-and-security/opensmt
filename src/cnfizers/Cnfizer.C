/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

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

#include "Cnfizer.h"

Cnfizer::Cnfizer( PtStore &      ptstore_
                , SMTConfig&     config_
                , SymStore&      symstore_
                , SStore&        sstore_
                , Logic&         logic_
                , TermMapper&    tmap_
                , THandler&      thandler_
                , SimpSMTSolver& solver_
                ) :
       ptstore  (ptstore_ )
     , config   (config_  )
     , symstore (symstore_)
     , sstore   (sstore_  )
     , logic    (logic_   )
     , tmap     (tmap_    )
     , thandler (thandler_)
     , solver   (solver_)
     , s_empty  (true)
     , status   (l_Undef)
{ }

void Cnfizer::initialize() {
    vec<Lit> c;
    Lit l = findLit(logic.getTerm_true());
    c.push(l);
    addClause(c);
    c.pop();
    l = findLit(logic.getTerm_false());
    c.push(~l);
    addClause(c);
}

// A term is literal if its sort is Bool and
//  (i)   number of arguments is 0
//  (ii)  its symbol is sym_NOT and argument is a literal (nested nots
//        create literals?)
//  (iii) it is an atom stating an equivalence of non-boolean terms (terms must be purified at this point)
bool Cnfizer::isLit(PTRef r) {
    Pterm& t = ptstore[r];
    if (symstore[t.symb()].rsort() == logic.getSort_bool()) {
        if (t.size() == 0) return true;
        if (t.symb() == logic.getSym_not() ) return isLit(t[0]);
        // At this point all arguments of equivalence have the same sort.  Check only the first
        if (logic.isEquality(r) && (symstore[ptstore[t[0]].symb()].rsort() != logic.getSort_bool())) return true;
        if (logic.isUP(r)) return true;
    }
    return false;
}

  // A term is an atom if its sort is Bool and
  //  (i)  number of arguments is 0, or
  //  (ii) it is an atom stating an equivalence of non-boolean terms (terms must be purified at this point)

// Extracts the literal corresponding to a term.
// Accepts negations.
const Lit Cnfizer::findLit(PTRef ptr) {
    PTRef p;
    bool sgn;
    Var v;
    tmap.getTerm(ptr, p, sgn);
    bool isnew = false;
    if (!seen.contains(p)) {
        v = solver.newVar();
        tmap.varToTheorySymbol.push(SymRef_Undef);
        tmap.varToTerm.push(PTRef_Undef);
        seen.insert(p, v);
        isnew = true;
    }
    else
        v = seen[p];

    Lit l = Lit(v, sgn);


    if (isnew) {
        if (logic.isTheoryTerm(p)) {
            Pterm& tr = ptstore[p];
            tmap.varToTheorySymbol[v] = tr.symb();
            tmap.theoryTerms.insert(p,true);
            assert(logic.isEquality(tr.symb())        ||
                   logic.isDisequality(tr.symb())     ||
                   logic.getTerm_true() == p          ||
                   logic.getTerm_false() == p         ||
                   logic.isUP(p)                      );
        }
        tmap.termToVar.insert(p, v);
//        tmap.varToTerm.insert(v, p);
        tmap.varToTerm[v] = p;
        if (logic.isTheoryTerm(p))
            solver.setFrozen(v, true);
#ifdef PEDANTIC_DEBUG
//        cerr << "Term " << logic.printTerm(p) << " maps to var " << v << endl;
#endif
    }
    return l;
}


// A term is an npatom if it is an atom or it is a negation of an npatom
bool Cnfizer::isNPAtom(PTRef r, PTRef& p) const {
    bool sign = false;
    while (true) {
        if (ptstore[r].symb() == logic.getSym_not() ) {
            r = ptstore[r][0];
            sign = !sign;
        }
        else {
            if (logic.isAtom(r))
                p = r;
            else
                p = PTRef_Undef;
            return sign;
        }
    }
}

//
// Main Routine. Examine formula and give it to the solver
//
lbool Cnfizer::cnfizeAndGiveToSolver( PTRef formula
#ifdef PRODUCE_PROOF
                                    , const ipartitions_t partition
#endif
                                    )
{
    Map<PTRef,PTRef,PTRefHash> dupMap;
//  egraph.initDupMap1( );

    if (solver.okay() == false) return l_False;

    assert( formula != PTRef_Undef);

    vec<PTRef> top_level_formulae;
    // Retrieve top-level formulae - this is a list constructed from a conjunction
    retrieveTopLevelFormulae(formula, top_level_formulae);
    assert(top_level_formulae.size() != 0);

    bool res = true;
    // For each top-level conjunct
    for (unsigned i = 0 ; i < top_level_formulae.size_() && (res == true) ; i ++) {
        PTRef f = top_level_formulae[i];
#ifdef PEDANTIC_DEBUG
        cout << "Adding clause " << logic.printTerm(f) << endl;
#endif
        // Give it to the solver if already in CNF
        if (checkCnf(f) == true || checkClause(f) == true) {
#ifdef PEDANTIC_DEBUG
            cout << " => Already in CNF" << endl;
#endif
            res = giveToSolver(f
#ifdef PRODUCE_PROOF
                              , partition
#endif
                              );
            continue;
        }

        // Check whether it can be rewritten using deMorgan laws

        else if (checkDeMorgan(f) == true) {
#ifdef PEDANTIC_DEBUG
            cout << " => Will be de Morganized" << endl;
#endif
            res = deMorganize(f
#ifdef PRODUCE_PROOF
                             , partition
#endif
                             );
        }
        else {
            // Otherwise perform cnfization
//            Map<PTRef, int, PTRefHash> ptref_to_incoming_edges;
            // The following tweak is able to use shared structure in "and"
            // and "or" subformulas.  I assume this is beneficial for the
            // efficiency of the solver.
//            computeIncomingEdges(f, ptref_to_incoming_edges);    // Compute incoming edges for f and children
//            f = rewriteMaxArity (f, ptref_to_incoming_edges);  // Rewrite f with maximum arity for operators
#ifdef PEDANTIC_DEBUG
            cout << " => proper cnfization" << endl;
#endif
            res = cnfize(f
#ifdef PRODUCE_PROOF
                        , partition
#endif
                        );                         // Perform actual cnfization (implemented in subclasses)
        }
        s_empty = false; // solver no longer empty
    }

//  egraph.doneDupMap1( );

    if (res == false) return l_False;

    return l_Undef;
}

lbool Cnfizer::extEquals(PTRef r_new, PTRef r_old) {

    Lit l_new = findLit(r_new);

    if (tmap.varToTheorySymbol[var(l_new)] == SymRef_Undef) {
        // The variable has already been removed
        return l_Undef;
    }

    Lit l_old = findLit(r_old);

    tmap.varToTheorySymbol[var(l_new)] = SymRef_Undef;
    tmap.theoryTerms.remove(r_new);

    lbool rval = l_Undef;

    vec<Lit> c1;
    vec<Lit> c2;
    c1.push(l_new); c1.push(~l_old);
    c2.push(~l_new); c2.push(l_old);
    rval = addClause(c1) == false ? l_False : l_Undef;
    if (rval == l_False) return rval;
    rval = addClause(c2) == false ? l_False : l_Undef;
    return rval;
}

//
// Apply simple de Morgan laws to the formula
//
bool Cnfizer::deMorganize( PTRef formula
#ifdef PRODUCE_PROOF
                         , const ipartitions_t & partition
#endif
                         )
{
    Pterm& pt = ptstore[formula];
    assert( pt.symb() != logic.getSym_and() );

    bool rval = true;

    //
    // Case (not (and a b)) --> (or (not a) (not b))
    //
    if (pt.symb() == logic.getSym_not() && ptstore[pt[0]].symb() == logic.getSym_and()) {

        PTRef and_tr = pt[0];
        // Retrieve conjuncts as a clause
        vec<Lit> clause;
        vec<PTRef> to_process;
        to_process.push(and_tr);

        while (to_process.size() != 0) {

            and_tr = to_process.last(); to_process.pop();
            Pterm& and_t = ptstore[and_tr];

            for (int i = 0; i < and_t.size(); i++) {

                PTRef  conj_tr = and_t[i];
                Pterm& conj_t  = ptstore[conj_tr];

                if (isLit(conj_tr)) {
                    clause.push(~findLit(conj_tr));
                }
                else if (conj_t.symb() == logic.getSym_and())
                    to_process.push(conj_tr);

                else assert(false);
            }
        }

#ifdef PRODUCE_PROOF
        if (config.produce_inter != 0)
            rval = addClause(clause, partition);
        else
#endif
            rval = addClause(clause);
    }
    return rval;
}

//
// Compute the number of incoming edges for e and children
//
void Cnfizer::computeIncomingEdges( PTRef e
                                  , Map<PTRef, int, PTRefHash> & ptref_to_incoming_edges )
{
  assert(e != PTRef_Undef);

  vec<PTRef> unprocessed_terms; // Stack for unprocessed enodes
  unprocessed_terms.push(e);    // formula needs to be processed
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while(unprocessed_terms.size() > 0) {
    PTRef tr = unprocessed_terms.last();
    // 
    // Skip if the node has already been processed before
    //
    if (ptref_to_incoming_edges.contains(tr)) {
        ptref_to_incoming_edges[tr]++;
        unprocessed_terms.pop();
        continue;
    }

    bool unprocessed_children = false;
    if (logic.isBooleanOperator(tr)) {
      Pterm& t = logic.getPterm(tr);
      for ( int i = 0; i < t.size(); i++) {
        //
        // Push only if it is an unprocessed boolean operator
        //
        if (!ptref_to_incoming_edges.contains(t[i])) {
            unprocessed_terms.push(t[i]);
            unprocessed_children = true;
        }
        else {
            ptref_to_incoming_edges[t[i]]++;
        }
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    //
    // At this point, every child has been processed
    //
    assert(logic.isBooleanOperator(tr) || logic.isAtom(tr));
    assert(!ptref_to_incoming_edges.contains(tr));
    ptref_to_incoming_edges.insert(tr, 1);
    unprocessed_terms.pop();
  }
}

//
// Rewrite formula with maximum arity for operators
//
PTRef Cnfizer::rewriteMaxArity(PTRef formula, Map<PTRef, int, PTRefHash> & ptref_to_incoming_edges )
{
  assert(formula != PTRef_Undef);

  vec<PTRef> unprocessed_terms;       // Stack for unprocessed PTRefs
  unprocessed_terms.push(formula);    // formula needs to be processed
  Map<PTRef,PTRef,PTRefHash> cache;   // Cache of processed nodes
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while(unprocessed_terms.size() != 0) {
    PTRef tr = unprocessed_terms.last();
    //
    // Skip if the node has already been processed before
    //
    if (cache.contains(tr)) {
      unprocessed_terms.pop();
      continue;
    }

    bool unprocessed_children = false;
    Pterm& t = logic.getPterm(tr);
    for (int i = 0; i < t.size(); i++) {

      //
      // Push only if it is an unprocessed boolean operator
      //
      if ( logic.isBooleanOperator(t[i]) && !cache.contains(t[i])) {
          unprocessed_terms.push(t[i]);
          unprocessed_children = true;
      }
      //
      // If it is an atom (either boolean or theory) just
      // store it in the cache
      //
      else if (logic.isAtom(t[i]))
        cache.insert(t[i], t[i]);

    }
    //
    // SKip if unprocessed_children
    //
    if (unprocessed_children)
      continue;

    unprocessed_terms.pop();
    PTRef result = PTRef_Undef;
    //
    // At this point, every child has been processed
    //
    assert(logic.isBooleanOperator(tr));

    // Construct the new lists for the operators
    if (logic.isAnd(tr) || logic.isOr(tr))
      result = mergeEnodeArgs( tr, cache, ptref_to_incoming_edges );
    else result = tr;

    assert(result != PTRef_Undef);
    assert(!cache.contains(tr));
    cache.insert(tr, result);
  }

  PTRef top_term = cache[formula];
  return top_term;
}

//
// Merge collected arguments for nodes
//
PTRef Cnfizer::mergeEnodeArgs( PTRef e
                             , Map<PTRef, PTRef, PTRefHash> & cache
                             , Map<PTRef, int, PTRefHash> & ptref_to_incoming_edges )
{
  assert( logic.isAnd(e) || logic.isOr(e) );

  Pterm& t = logic.getPterm(e);
  SymRef e_symb = t.symb();
  vec<PTRef> new_args;

  for (int i = 0; i < t.size(); i++) {
    PTRef arg = t[i];
    PTRef sub_arg = cache[arg];
    SymRef sym = logic.getPterm(arg).symb();

    // We're no longer looking at either or or an and.  I hope I got this right...
    if (sym != e_symb) {
      new_args.push(sub_arg);
      continue;
    }

    assert(ptref_to_incoming_edges.contains(arg));
    assert(ptref_to_incoming_edges[arg] >= 1 );

    if (ptref_to_incoming_edges[arg] > 1) {
      new_args.push(sub_arg);
      continue;
    }

    Pterm& s = logic.getPterm(sub_arg);
    for (int j = 0; j < s.size(); j++)
        new_args.push(s[j]);
  }


  // This creates a new term with the same symbol having the arguments from new_args
  // We know that e is either and or or
  return logic.isAnd(e) ? logic.mkAnd(new_args) : logic.mkOr(new_args);
}

//
// Check whether a formula is in cnf
//

bool Cnfizer::checkCnf(PTRef formula) {
    bool res = checkConj(formula);
    if (res == false) return checkClause(formula);
    return res;
}


//
// Check if a formula is a conjunction of clauses
//

bool Cnfizer::checkConj(PTRef e)
{
    if (isLit(e)) // A Boolean constant
        return true;

    Pterm& and_t = ptstore[e];


    if (and_t.symb() != logic.getSym_and())
        return false;

    vec<PTRef> to_process;
    to_process.push(e);
    while (to_process.size() != 0) {

        e = to_process.last(); to_process.pop();

        and_t = ptstore[e];

        for (int i = 0; i < and_t.size(); i++) {
            if (ptstore[and_t[i]].symb() == logic.getSym_and())
                to_process.push(and_t[i]);
            else if (!checkClause(and_t[i])) // Slightly awkward to use the same cache...
                return false;
        }

    }

    return true;
}


//
// Check whether a formula is a clause
//

bool Cnfizer::checkClause(PTRef e)
{
    assert(e != PTRef_Undef);

    Pterm& or_t = ptstore[e];
    if (or_t.symb() != logic.getSym_or())
        return false;

    vec<PTRef> to_process;

    to_process.push(e);

    while (to_process.size() != 0) {

        e = to_process.last(); to_process.pop();

        Pterm& or_t = ptstore[e];
        for (int i = 0; i < or_t.size(); i++) {
            Pterm& arg = ptstore[or_t[i]];
            if (arg.symb() == logic.getSym_or())
                to_process.push(or_t[i]);
            else {
                PTRef p;
                isNPAtom(or_t[i], p);
                if (p == PTRef_Undef)
                    return false;
            }
        }
    }

    return true;
}


/*
void Cnfizer::declareAtom(PTRef ptr, TRef symb) {
    if (!processed.contains(ptr)) {
        processed.insert(ptr, Lit(solver.newVar()));
        if (symb == sym_TRUE) {
            vec<Lit> cl_true;
            cl_true.push(findLit(ptr));
            bool rval = solver.addSMTClause(cl_true);
            solver.setFrozen(var(findLit(ptr)), true);
            assert(rval);
        }
        else if (symb == sym_FALSE) {
            vec<Lit> cl_false;
            cl_false.push(~findLit(ptr));
            bool rval = solver.addSMTClause(cl_false);
            solver.setFrozen(var(findLit(ptr)), false);
            assert(rval);
        }
    }
}
*/

/*
Lit Cnfizer::getPureTerm(PTRef r) const {
    PTRef p;
    bool sgn;
    getPureTerm(r, p, sgn); // remove the negations and compute the sign
}
*/

//
// Check whether it can be easily put in clausal form by means of DeMorgan's Rules
//
bool Cnfizer::checkDeMorgan(PTRef e)
{
    Map<PTRef,bool,PTRefHash,Equal<PTRef> > check_cache;
    Pterm& not_t = ptstore[e];
    if ( not_t.symb() == logic.getSym_not() && checkPureConj(not_t[0], check_cache) ) return true;
    else return false;
}

//
// Check whether it is a pure conjunction of literals
//
bool Cnfizer::checkPureConj(PTRef e, Map<PTRef,bool,PTRefHash,Equal<PTRef> > & check_cache) {
    if (check_cache.contains(e))
        return true;

    vec<PTRef> to_process;
    to_process.push(e);

    // Topmost needs to be and
    if (ptstore[e].symb() != logic.getSym_and()) return false;

    while (to_process.size() != 0) {
        e = to_process.last(); to_process.pop();
        Pterm& and_t = ptstore[e];

        if (and_t.symb() == logic.getSym_and())
            for (int i = 0; i < and_t.size(); i++)
                to_process.push(and_t[i]);
        else if (!isLit(e))
            return false;

        check_cache.insert(e, true);
    }

    return true;
}

#ifndef PRODUCE_PROOF
bool Cnfizer::addClause( vec<Lit>& c ) {
#else
bool Cnfizer::addClause( vec<Lit>& c const ipartitions_t& partition) {
#endif
#ifdef PEDANTIC_DEBUG
//    cerr << "Adding clause ";
//    for (int i = 0; i < c.size(); i++)
//        cerr << (sign(c[i]) ? "not " : "")
//             << logic.printTerm(tmap.varToTerm[var(c[i])])
//             << " ";
//    cerr << endl;
#endif
#ifndef PRODUCE_PROOF
    return solver.addSMTClause(c);
#else
    return solver.addSMTClause(c, partition);
#endif
}
//
// Give the formula to the solver
//
bool Cnfizer::giveToSolver( PTRef f
#ifdef PRODUCE_PROOF
                          , const ipartitions_t & partition
#endif
                          )
{
    vec<Lit> clause;

    //
    // A unit clause
    //
    if (isLit(f)) {
        clause.push(findLit(f));
#ifdef PRODUCE_PROOF
        if ( config.produce_inter != 0 )
            return addClause( clause, partition );
#endif
        return addClause( clause );
    }
    //
    // A clause
    //
    Pterm& cand_t = ptstore[f];

    if (cand_t.symb() == logic.getSym_or()) {
        vec<PTRef> queue;
        queue.push(f);
        while (queue.size() != 0) {
            Pterm& e = ptstore[queue.last()];
            queue.pop();
            for (int i = 0; i < e.size(); i ++) {
                if (isLit(e[i]))
                    clause.push(findLit(e[i]));
                else if (ptstore[e[i]].symb() == logic.getSym_or())
                    queue.push(e[i]);
                else
                    assert(false); // Not a clause!
            }
        }
#ifdef PRODUCE_PROOF
        if ( config.produce_inter != 0 )
            return addClause(f, partition);
#endif
        return addClause(clause);
    }

    //
    // Conjunction
    //
    assert(cand_t.symb() == logic.getSym_and());
    vec<PTRef> conj;
    retrieveTopLevelFormulae( f, conj );
    bool result = true;
    for (unsigned i = 0; i < conj.size_( ) && result; i++)
        result = giveToSolver(conj[i]
#ifdef PRODUCE_PROOF
                             , partition
#endif
                             );
    return result;
}

//
// Retrieve the formulae at the top-level
//
void Cnfizer::retrieveTopLevelFormulae(PTRef f, vec<PTRef>& top_level_formulae)
{
    vec<PTRef> to_process;

    to_process.push(f);
    while (to_process.size() != 0) {
        f = to_process.last(); to_process.pop();
        Pterm& cand_t = ptstore[f];
        if (cand_t.symb() == logic.getSym_and())
            for (int i = cand_t.size() - 1; i >= 0; i--)
                to_process.push(cand_t[i]);
        else top_level_formulae.push(f);
    }
}

//
// Retrieve a clause
//
//void Cnfizer::retrieveClause( Enode * f, vector< Enode * > & clause )
//{
//  assert( f->isLit( ) || f->isOr( ) );
//
//  if ( f->isLit( ) )
//  {
//    clause.push_back( f );
//  }
//  else if ( f->isOr( ) )
//  {
//    for ( Enode * list = f->getCdr( ) ; 
//	  list != egraph.enil ; 
//	  list = list->getCdr( ) )
//      retrieveClause( list->getCar( ), clause );
//  }
//}

//
// Retrieve conjuncts
//
//void Cnfizer::retrieveConjuncts( Enode * f, vector< Enode * > & conjuncts )
//{
//  assert( f->isLit( ) || f->isAnd( ) );
//
//  if ( f->isLit( ) )
//  {
//    conjuncts.push_back( f );
//  }
//  else if ( f->isAnd( ) )
//  {
//    for ( Enode * list = f->getCdr( ) ; 
//	  list != egraph.enil ; 
//	  list = list->getCdr( ) )
//      retrieveConjuncts( list->getCar( ), conjuncts );
//  }
//}

//
// A shortcut for literal negation
//
//Enode * Cnfizer::toggleLit ( Enode * arg )
//{
//  assert( arg->isTerm( ) );
//  return egraph.mkNot( egraph.cons( arg ) );
//}


vec<ValPair>* Cnfizer::getModel() {
    assert(solver.okay());
    vec<lbool>& model = solver.model;
    vec<ValPair>* out = new vec<ValPair>();
    for (Var v = 0; v < model.size(); v++) {
        if (tmap.varToTerm[v] != PTRef_Undef)
            out->push(ValPair(tmap.varToTerm[v], model[v]));
    }
    return out;
}

lbool Cnfizer::getTermValue(PTRef tr) {
    assert(solver.okay());
    assert(status == l_True);
    vec<lbool>& model = solver.model;
    PTRef p;
    bool sgn;
    tmap.getTerm(tr, p, sgn);
    Var v = tmap.termToVar[p];
    lbool val = model[v];
    assert(val != l_Undef);

    return sgn == false ? val : (val == l_True ? l_False : l_True);
}

// Assumes that the root of the tree is the last element of term_list
PTRef Cnfizer::expandItes(vec<PtChild>& term_list) {
    assert(term_list.size() > 0);
    vec<PtPair> ites;
    int l = term_list.size()-1;
    assert(!logic.isTheoryTerm(term_list[l].tr) or !logic.isIte(logic.getPterm(term_list[l].tr).symb()));

    for (int i = 0; i < term_list.size()-1; i++) {
        PtChild ptc   = term_list[i];
        Pterm& parent = logic.getPterm(ptc.parent);
        PTRef tr      = ptc.tr;
        int pos       = ptc.pos;
        Pterm& pt     = logic.getPterm(tr);

        if (logic.isTheoryTerm(tr) and logic.isIte(pt.symb())) {
            // (1) Add a new term o_ite with no arguments and same sort as pt
            // (2) add tr to ites
            // (3) replace parent[pos] with o_ite
            SRef sr = logic.getSym(pt.symb()).rsort();
            char* name;
            asprintf(&name, ".oite%d", logic.getPterm(tr).getId());
            PTRef o_ite = logic.mkConst(sr, name);
            // The old term goes to PtPair
            ites.push(PtPair(tr, o_ite));
#ifdef PEDANTIC_DEBUG
            cerr << "Added the term " << logic.printTerm(tr) << " to later processing" << endl;
            cerr << "; changing " << logic.printTerm(parent[pos]) << " to ";
#endif
            parent[pos] = o_ite;
#ifdef PEDANTIC_DEBUG
            cerr << logic.printTerm(parent[pos]) << endl;
#endif
        }
    }

    vec<PTRef> ite_roots;
    ite_roots.push(term_list[l].tr);

    for (int j = 0; j < ites.size(); j++) {
        PTRef ite  = ites[j].x;
        PTRef sbst = ites[j].y;
        PTRef b = logic.getPterm(ite)[0];
        PTRef t = logic.getPterm(ite)[1];
        PTRef e = logic.getPterm(ite)[2];

        // b -> (= sbst t)
        vec<PTRef> args_eq;
        args_eq.push(sbst);
        args_eq.push(t);
        PTRef eq_term = logic.mkEq(args_eq);
        assert(eq_term != PTRef_Undef);
        vec<PTRef> args_impl;
        args_impl.push(b);
        args_impl.push(eq_term);
        PTRef if_term = logic.mkImpl(args_impl);
        assert(if_term != PTRef_Undef);
        // \neg b -> (= sbst e)
        vec<PTRef> args_eq2;
        args_eq2.push(sbst);
        args_eq2.push(e);
        PTRef eq_term2 = logic.mkEq(args_eq2);
        assert(eq_term2 != PTRef_Undef);
        PTRef neg_term = logic.mkNot(b);
        vec<PTRef> args_impl2;
        args_impl2.push(neg_term);
        args_impl2.push(eq_term2);

        PTRef else_term = logic.mkImpl(args_impl2);
        assert(else_term != PTRef_Undef);

        ite_roots.push(if_term);
        ite_roots.push(else_term);
    }
    if (ite_roots.size() > 1)
        return logic.mkAnd(ite_roots);
    else return term_list[l].tr;
}
