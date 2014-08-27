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
//bool Cnfizer::isLit(PTRef r) {
//    Pterm& t = ptstore[r];
//    if (symstore[t.symb()].rsort() == logic.getSort_bool()) {
//        if (t.size() == 0) return true;
//        if (t.symb() == logic.getSym_not() ) return isLit(t[0]);
//        // At this point all arguments of equivalence have the same sort.  Check only the first
//        if (logic.isEquality(r) && (symstore[ptstore[t[0]].symb()].rsort() != logic.getSort_bool())) return true;
//        if (logic.isUP(r)) return true;
//    }
//    return false;
//}

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
            Pterm& t = ptstore[p];
            tmap.varToTheorySymbol[v] = t.symb();
//            tmap.theoryTerms.insert(p,true);
            assert(logic.isEquality(t.symb())        ||
                   logic.isDisequality(t.symb())     ||
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
    Map<PTRef,PTRef,PTRefHash> valdupmap;
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
        cerr << "Adding clause " << logic.printTerm(f) << endl;
#endif
        // Give it to the solver if already in CNF
        if (checkCnf(f) == true || checkClause(f) == true) {
#ifdef PEDANTIC_DEBUG
            cerr << " => Already in CNF" << endl;
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
#endif // PEDANTIC_DEBUG
#ifdef ENABLE_SHARING_BUG
            res = cnfize(f, valdupmap);
#else // ENABLE_SHARING_BUG
#ifdef PRODUCE_PROOF
            res = cnfize(f, partition);
#else // PRODUCE_PROOF
            res = cnfize(f);                         // Perform actual cnfization (implemented in subclasses)
#endif // PRODUCE_PROOF
#endif // ENABLE_SHARING_BUG
        }
        s_empty = false; // solver no longer empty
    }

//  egraph.doneDupMap1( );

    if (res == false) return l_False;

    return l_Undef;
}

/*
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
*/
//
// Apply simple de Morgan laws to the formula
//
bool Cnfizer::deMorganize( PTRef formula
#ifdef PRODUCE_PROOF
                         , const ipartitions_t & partition
#endif
                         )
{
    assert(!logic.isAnd(formula));
    Pterm& pt = ptstore[formula];

    bool rval = true;

    //
    // Case (not (and a b)) --> (or (not a) (not b))
    //
    if (logic.isNot(formula) && logic.isAnd(pt[0])) {
        vec<PTRef> conjuncts;
        vec<Lit> clause;

        retrieveConjuncts(pt[0], conjuncts);
        for (int i = 0; i < conjuncts.size(); i++) {
            clause.push(~findLit(conjuncts[i]));
#ifdef PEDANTIC_DEBUG
            cerr << "(not " << logic.printTerm(conjuncts[i]) << ")" << endl;
#endif
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
    if (logic.isLit(e)) // A Boolean constant
        return true;

    Pterm& and_t = ptstore[e];


    if (and_t.symb() != logic.getSym_and())
        return false;

    vec<PTRef> to_process;
    to_process.push(e);
    while (to_process.size() != 0) {

        e = to_process.last(); to_process.pop();

        Pterm& and_t = ptstore[e];

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
        else if (!logic.isLit(e))
            return false;

        check_cache.insert(e, true);
    }

    return true;
}

#ifndef PRODUCE_PROOF
bool Cnfizer::addClause( vec<Lit>& c )
#else
bool Cnfizer::addClause( vec<Lit>& c const ipartitions_t& partition)
#endif
{
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
    if (logic.isLit(f)) {
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
        vec<PTRef> lits;
        retrieveClause(f, lits);
        for (int i = 0; i < lits.size(); i++)
            clause.push(findLit(lits[i]));
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
// Retrieve the formulae at the top-level.  Ignore duplicates
//
void Cnfizer::retrieveTopLevelFormulae(PTRef f, vec<PTRef>& top_level_formulae)
{
    vec<PTRef> to_process;

    Map<PTRef,bool,PTRefHash> seen;

    to_process.push(f);
    while (to_process.size() != 0) {
        f = to_process.last(); to_process.pop();
        Pterm& cand_t = ptstore[f];
        if (cand_t.symb() == logic.getSym_and())
            for (int i = cand_t.size() - 1; i >= 0; i--)
                to_process.push(cand_t[i]);
        else if (!seen.contains(f)) {
            top_level_formulae.push(f);
            seen.insert(f, true);
        }
    }
}

//
// Retrieve a clause
//
void Cnfizer::retrieveClause( PTRef f, vec<PTRef> & clause )
{
    assert(logic.isLit(f) || logic.isOr(f));

    if ( logic.isLit(f) )
        clause.push(f);
    else if ( logic.isOr(f) ) {
        Pterm& t = logic.getPterm(f);
        for ( int i = 0; i < t.size(); i++)
            retrieveClause( t[i], clause );
    }
}

//
// Retrieve conjuncts
//
void Cnfizer::retrieveConjuncts( PTRef f, vec<PTRef> & conjuncts )
{
    assert(logic.isLit(f) || logic.isAnd(f));

    if (logic.isLit(f))
        conjuncts.push(f);
    else {
        Pterm& t = logic.getPterm(f);
        for (int i = 0; i < t.size(); i++)
            retrieveConjuncts(t[i], conjuncts);
    }
}

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
    if (tmap.termToVar.contains(p)) {
        Var v = tmap.termToVar[p];
        lbool val = model[v];
        assert(val != l_Undef);
        return sgn == false ? val : (val == l_True ? l_False : l_True);
    }
    else return l_Undef;
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

void Cnfizer::getCnfState(CnfState& cs)
{
    char* out = (char*)malloc(1);
    out[0] = 0;
    // The cnf
    solver.cnfToString(cs);
//    cs.setCnf(solver.cnfToString());
//    if (!solver.okay()) {
//        char* tmp = cs.cnf;
//        asprintf(&cs.cnf, "%s\n%s 0", tmp, solver.litToString(~Lit(tmap.termToVar[logic.getTerm_true()])));
//    }

    // The mapping to terms
#ifdef PEDANTIC_DEBUG
    char* old;
#endif
    for (int i = 0; i < solver.nVars(); i++) {
        PTRef tr = tmap.varToTerm[i];
        cs.addToMap({i, tr});
#ifdef PEDANTIC_DEBUG
        old = out;
        char* map_s;
        char* term_s = logic.printTerm(tmap.varToTerm[i]);
        asprintf(&map_s, "%d -> %d [%s]", i, tmap.varToTerm[i].x, term_s);
        free(term_s);
        asprintf(&out, "%s%s\n", old, map_s);
        free(map_s);
#endif
    }

    // The terms, starting from the boolean theory terms found from the cnf
//    Map<PTRef, bool, PTRefHash> seen;
//    vec<PTRef> queue;
//    bool_thterms.copyTo(queue);
//    while (queue.size() != 0) {
//        PTRef tr = queue.last();
//        queue.pop();
//        if (seen.contains(tr))
//            continue;
//        Pterm& t = logic.getPterm(tr);
//        char* t_str;
//        if (t.size() > 0) {
//            asprintf(&t_str, "%d[", tr.x);
//            for (int i = 0; i < t.size(); i++) {
//                char* t_old = t_str;
//                asprintf(&t_str, "%s%d ", t_old, t[i].x);
//                free(t_old);
//                queue.push(t[i]);
//            }
//            t_str[strlen(t_str)-1] = ']';
//        } else
//            asprintf(&t_str, "%d[]", tr.x);
//
//        old = out;
//        asprintf(&out, "%s\n%s", old, t_str);
//        free(old);
//        seen.insert(tr, true);
//    }
#ifdef PEDANTIC_DEBUG
    cerr << "Cnf looks like" << endl;
    cerr << cs.cnf << endl;
    cerr << "Map looks like " << endl;
    cerr << out << endl;
    free(out);
#endif
}
