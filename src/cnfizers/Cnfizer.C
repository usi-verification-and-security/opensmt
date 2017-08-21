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

#include <queue>

using namespace std;

Cnfizer::Cnfizer ( SMTConfig       &config_
                   , Theory        &theory
                   , TermMapper    &tmap
                   , THandler      &thandler_
                   , SimpSMTSolver &solver_
                 ) :
    config   (config_  )
    , theory   (theory)
    , logic    (theory.getLogic())
    , tmap     (tmap)
    , thandler (thandler_)
    , solver   (solver_)
    , s_empty  (true)
{
    frame_terms.push(logic.getTerm_true()); // frame 0 does not have a var
    frame_term = frame_terms[0];
}

void Cnfizer::initialize()
{
    vec<Lit> c;
    Lit l = theory.findLit (logic.getTerm_true());
    c.push (l);
    addClause (c);
    c.pop();
    l = theory.findLit (logic.getTerm_false());
    c.push (~l);
    addClause (c);
}

lbool
Cnfizer::solve(vec<FrameId>& en_frames)
{
    vec<Lit> assumps;
    // Initialize so that by default frames are disabled
    for (int i = 0; i < frame_terms.size(); i++)
        assumps.push(theory.findLit(frame_terms[i]));

    // Enable the terms which are listed in en_frames
    // At this point assumps has the same size as frame_terms and the
    // elements are in the same order.  We simply invert the
    // corresponding literals
    for (int i = 0; i < en_frames.size(); i++) {
        int asmp_idx = en_frames[i].id;
        assumps[asmp_idx] = ~assumps[asmp_idx];
    }
    // Filter out the lit_Trues and lit_Falses used as empty values
    Lit lit_true = theory.findLit(logic.getTerm_true());
    int i, j;
    for (i = j = 0; i < assumps.size(); i++) {
        if (assumps[i] != lit_true && assumps[i] != ~lit_true)
            assumps[j++] = assumps[i];
    }
    assumps.shrink(i-j);
    return solver.solve(assumps, !config.isIncremental(), config.isIncremental());

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


// A term is an npatom if it is an atom or it is a negation of an npatom
bool Cnfizer::isNPAtom (PTRef r, PTRef &p) const
{
    bool sign = false;

    while (true)
    {
        if (logic.isNot (r))
        {
            r = logic.getPterm (r)[0];
            sign = !sign;
        }
        else
        {
            if (logic.isAtom (r))
                p = r;
            else
                p = PTRef_Undef;

            return sign;
        }
    }
}

void Cnfizer::setFrameTerm(FrameId frame_id)
{
    while (frame_terms.size() <= frame_id.id) {
        frame_terms.push(logic.getTerm_true());
    }
    // frame_id == {0} is for the bottom frame and we don't want to add
    // literals to it since it is never retracted.
    if (frame_id != FrameId_bottom && frame_terms[frame_id.id] == logic.getTerm_true()) {
        char* name;
        asprintf(&name, "%s%d", Logic::s_framev_prefix, frame_id.id);
        PTRef frame_term = logic.mkBoolVar(name);
        free(name);
        frame_terms[frame_id.id] = frame_term;
    }

    frame_term = frame_terms[frame_id.id];
}

//
// Main Routine. Examine formula and give it to the solver
//
lbool Cnfizer::cnfizeAndGiveToSolver(PTRef formula, FrameId frame_id)
{
    // Get the variable for the incrementality.
    setFrameTerm(frame_id);

    Map<PTRef, PTRef, PTRefHash> valdupmap;
//  egraph.initDupMap1( );

    if (solver.okay() == false) return l_False;

    assert ( formula != PTRef_Undef);

#ifdef PEDANTIC_DEBUG
    cerr << "cnfizerAndGiveToSolver: " << logic.printTerm (formula) << endl;
#endif

    vec<PTRef> top_level_formulae;
    // Retrieve top-level formulae - this is a list constructed from a conjunction
    retrieveTopLevelFormulae (formula, top_level_formulae);
    assert (top_level_formulae.size() != 0);

#ifdef PEDANTIC_DEBUG
    cerr << "Top level formulae:" << endl;

    for (unsigned i = 0; i < top_level_formulae.size_(); i++)
        cerr << "Top level formula " << i << ": " << logic.printTerm (top_level_formulae[i]) << endl;

#endif

    bool res = true;

    // For each top-level conjunct
    for (unsigned i = 0 ; i < top_level_formulae.size_() && (res == true) ; i ++)
    {
        PTRef f = top_level_formulae[i];
#ifdef PEDANTIC_DEBUG
        cerr << "Adding clause " << logic.printTerm (f) << endl;
#endif

#ifdef PRODUCE_PROOF
        ipartitions_t mask = 0;
        if (logic.canInterpolate())
        {
            // Create mask to spread among all literals created for this PTRef
            if (logic.isAssertion (f)) //if f is an assertion, one bit is set
            {
                mask += 1;
                mask <<= (logic.assertionIndex (f) + 1);
            }

            else if(f == logic.getTerm_true() || f == logic.getTerm_false())
            {
                mask = 1;
                mask = ~mask;
            }

            else //f may have been flattened etc
            {
                PTRef root_tmp = logic.getOriginalAssertion(f);
                assert(!logic.hasOriginalAssertion(root_tmp));
                mask = logic.getIPartitions(root_tmp);

//                logic.setIPartitions (f, 0);
                logic.addIPartitions (f, mask);
            }

            assert (mask != 0);
#ifdef PEDANTIC_DEBUG
            cerr << "Spreading mask " << mask << endl;
#endif // PEDANTIC_DEBUG
        }
#endif // PRODUCE_PROOF

        // Give it to the solver if already in CNF
        if (checkCnf (f) == true || checkClause (f) == true)
        {
#ifdef PEDANTIC_DEBUG
            cerr << " => Already in CNF" << endl;
#endif
#ifdef PRODUCE_PROOF
            res = giveToSolver (f, mask);
#else
            res = giveToSolver (f);
#endif
            continue;
        }

        // Check whether it can be rewritten using deMorgan laws

        else if (checkDeMorgan (f) == true)
        {
#ifdef PEDANTIC_DEBUG
            cout << " => Will be de Morganized" << endl;
#endif
#ifdef PRODUCE_PROOF
            res = deMorganize (f, mask);
#else
            res = deMorganize (f);
#endif
        }
        else
        {
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
#ifdef PRODUCE_PROOF
            res = cnfize (f, mask);
#else // PRODUCE_PROOF
            res = cnfize (f);                        // Perform actual cnfization (implemented in subclasses)
#endif // PRODUCE_PROOF
        }

        s_empty = false; // solver no longer empty
    }

//  egraph.doneDupMap1( );

    if (res == false) return l_False;

    return l_Undef;
}

/*
lbool Cnfizer::extEquals(PTRef r_new, PTRef r_old) {

    Lit l_new = theory.findLit(r_new);

    if (tmap.varToTheorySymbol[var(l_new)] == SymRef_Undef) {
        // The variable has already been removed
        return l_Undef;
    }

    Lit l_old = theory.findLit(r_old);

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
#ifdef PRODUCE_PROOF
bool Cnfizer::deMorganize ( PTRef formula, const ipartitions_t &mask)
#else
bool Cnfizer::deMorganize ( PTRef formula )
#endif
{
    assert (!logic.isAnd (formula));
    Pterm &pt = logic.getPterm (formula);

    bool rval = true;

    //
    // Case (not (and a b)) --> (or (not a) (not b))
    //
    if (logic.isNot (formula) && logic.isAnd (pt[0]))
    {
        vec<PTRef> conjuncts;
        vec<Lit> clause;

        retrieveConjuncts (pt[0], conjuncts);

        for (int i = 0; i < conjuncts.size(); i++)
        {
            clause.push (~theory.findLit (conjuncts[i]));
#ifdef PEDANTIC_DEBUG
            cerr << "(not " << logic.printTerm (conjuncts[i]) << ")" << endl;
#endif
        }

#ifdef PRODUCE_PROOF
        rval = addClause (clause, mask);
#else
        rval = addClause (clause);
#endif
    }

    return rval;
}

//
// Compute the number of incoming edges for e and children
//
void Cnfizer::computeIncomingEdges ( PTRef e
                                     , Map<PTRef, int, PTRefHash> &ptref_to_incoming_edges )
{
    assert (e != PTRef_Undef);

    vec<PTRef> unprocessed_terms; // Stack for unprocessed enodes
    unprocessed_terms.push (e);   // formula needs to be processed

    //
    // Visit the DAG of the formula from the leaves to the root
    //
    while (unprocessed_terms.size() > 0)
    {
        PTRef tr = unprocessed_terms.last();

        //
        // Skip if the node has already been processed before
        //
        if (ptref_to_incoming_edges.has (tr))
        {
            ptref_to_incoming_edges[tr]++;
            unprocessed_terms.pop();
            continue;
        }

        bool unprocessed_children = false;

        if (logic.isBooleanOperator (tr))
        {
            Pterm &t = logic.getPterm (tr);

            for ( int i = 0; i < t.size(); i++)
            {
                //
                // Push only if it is an unprocessed boolean operator
                //
                if (!ptref_to_incoming_edges.has (t[i]))
                {
                    unprocessed_terms.push (t[i]);
                    unprocessed_children = true;
                }
                else
                {
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
        assert (logic.isBooleanOperator (tr) || logic.isAtom (tr));
        assert (!ptref_to_incoming_edges.has (tr));
        ptref_to_incoming_edges.insert (tr, 1);
        unprocessed_terms.pop();
    }
}

//
// Rewrite formula with maximum arity for operators
//
PTRef Cnfizer::rewriteMaxArity (PTRef formula, Map<PTRef, int, PTRefHash> &ptref_to_incoming_edges )
{
    assert (formula != PTRef_Undef);

    vec<PTRef> unprocessed_terms;       // Stack for unprocessed PTRefs
    unprocessed_terms.push (formula);   // formula needs to be processed
    Map<PTRef, PTRef, PTRefHash> cache; // Cache of processed nodes

    //
    // Visit the DAG of the formula from the leaves to the root
    //
    while (unprocessed_terms.size() != 0)
    {
        PTRef tr = unprocessed_terms.last();

        //
        // Skip if the node has already been processed before
        //
        if (cache.has (tr))
        {
            unprocessed_terms.pop();
            continue;
        }

        bool unprocessed_children = false;
        Pterm &t = logic.getPterm (tr);

        for (int i = 0; i < t.size(); i++)
        {

            //
            // Push only if it is an unprocessed boolean operator
            //
            if ( logic.isBooleanOperator (t[i]) && !cache.has (t[i]))
            {
                unprocessed_terms.push (t[i]);
                unprocessed_children = true;
            }
            //
            // If it is an atom (either boolean or theory) just
            // store it in the cache
            //
            else if (logic.isAtom (t[i]))
                cache.insert (t[i], t[i]);

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
        assert (logic.isBooleanOperator (tr));

        // Construct the new lists for the operators
        if (logic.isAnd (tr) || logic.isOr (tr))
            result = mergeEnodeArgs ( tr, cache, ptref_to_incoming_edges );
        else result = tr;

        assert (result != PTRef_Undef);
        assert (!cache.has (tr));
        cache.insert (tr, result);
    }

    PTRef top_term = cache[formula];
    return top_term;
}

//
// Merge collected arguments for nodes
//
PTRef Cnfizer::mergeEnodeArgs ( PTRef e
                                , Map<PTRef, PTRef, PTRefHash> &cache
                                , Map<PTRef, int, PTRefHash> &ptref_to_incoming_edges )
{
    assert ( logic.isAnd (e) || logic.isOr (e) );

    Pterm &t = logic.getPterm (e);
    SymRef e_symb = t.symb();
    vec<PTRef> new_args;

    for (int i = 0; i < t.size(); i++)
    {
        PTRef arg = t[i];
        PTRef sub_arg = cache[arg];
        SymRef sym = logic.getPterm (arg).symb();

        // We're no longer looking at either or or an and.  I hope I got this right...
        if (sym != e_symb)
        {
            new_args.push (sub_arg);
            continue;
        }

        assert (ptref_to_incoming_edges.has (arg));
        assert (ptref_to_incoming_edges[arg] >= 1 );

        if (ptref_to_incoming_edges[arg] > 1)
        {
            new_args.push (sub_arg);
            continue;
        }

        Pterm &s = logic.getPterm (sub_arg);

        for (int j = 0; j < s.size(); j++)
            new_args.push (s[j]);
    }


    // This creates a new term with the same symbol having the arguments from new_args
    // We know that e is either and or or
    return logic.isAnd (e) ? logic.mkAnd (new_args) : logic.mkOr (new_args);
}

//
// Check whether a formula is in cnf
//

bool Cnfizer::checkCnf (PTRef formula)
{
    bool res = checkConj (formula);

    if (res == false) return checkClause (formula);

    return res;
}


//
// Check if a formula is a conjunction of clauses
//

bool Cnfizer::checkConj (PTRef e)
{
    if (logic.isLit (e)) // A Boolean constant
        return true;

    Pterm &and_t = logic.getPterm (e);


    if (and_t.symb() != logic.getSym_and())
        return false;

    vec<PTRef> to_process;
    to_process.push (e);

    while (to_process.size() != 0)
    {

        e = to_process.last();
        to_process.pop();

        Pterm &and_t = logic.getPterm (e);

        for (int i = 0; i < and_t.size(); i++)
        {
            if (logic.isAnd (and_t[i]))
                to_process.push (and_t[i]);
            else if (!checkClause (and_t[i])) // Slightly awkward to use the same cache...
                return false;
        }

    }

    return true;
}


//
// Check whether a formula is a clause
//

bool Cnfizer::checkClause (PTRef e)
{
    assert (e != PTRef_Undef);

    if (!logic.isOr (e))
        return false;

    vec<PTRef> to_process;

    to_process.push (e);

    while (to_process.size() != 0)
    {

        e = to_process.last();
        to_process.pop();

        Pterm &or_t = logic.getPterm (e);

        for (int i = 0; i < or_t.size(); i++)
        {
            if (logic.isOr (or_t[i]))
                to_process.push (or_t[i]);
            else
            {
                PTRef p;
                isNPAtom (or_t[i], p);

                if (p == PTRef_Undef)
                    return false;
            }
        }
    }

    return true;
}



//
// Check whether it can be easily put in clausal form by means of DeMorgan's Rules
//
bool Cnfizer::checkDeMorgan (PTRef e)
{
    Map<PTRef, bool, PTRefHash, Equal<PTRef> > check_cache;
    Pterm &not_t = logic.getPterm (e);

    if (logic.isNot (e) && checkPureConj (not_t[0], check_cache) ) return true;
    else return false;
}

//
// Check whether it is a pure conjunction of literals
//
bool Cnfizer::checkPureConj (PTRef e, Map<PTRef, bool, PTRefHash, Equal<PTRef> > &check_cache)
{
    if (check_cache.has (e))
        return true;

    vec<PTRef> to_process;
    to_process.push (e);

    // Topmost needs to be and
    if (!logic.isAnd (e)) return false;

    while (to_process.size() != 0)
    {
        e = to_process.last();
        to_process.pop();
        Pterm &and_t = logic.getPterm (e);

        if (logic.isAnd (e))
            for (int i = 0; i < and_t.size(); i++)
                to_process.push (and_t[i]);
        else if (!logic.isLit (e))
            return false;

        check_cache.insert (e, true);
    }

    return true;
}

#ifdef PRODUCE_PROOF
bool Cnfizer::addClause ( const vec<Lit> &c_in, const ipartitions_t &mask)
#else
bool Cnfizer::addClause ( const vec<Lit> &c_in )
#endif
{

    vec<Lit> c;
    c_in.copyTo(c);
    if (frame_term != logic.getTerm_true()) {
        Lit l = theory.findLit(frame_term);
        tmap.setFrozen(var(l));
        c.push(l);
    }

#ifdef PEDANTIC_DEBUG
    cerr << "== clause start" << endl;

    for (int i = 0; i < c.size(); i++)
    {
        cerr << "(" << c[i].x << "," << var (c[i]) << ") * " << (sign (c[i]) ? "not " : "")
             << logic.printTerm (tmap.varToPTRef (var (c[i])))
             << " ";
        cerr << endl;
    }

#endif
#ifdef PRODUCE_PROOF
    bool res = solver.addSMTClause (c, mask);
#else
    bool res = solver.addSMTClause (c);
#endif
    return res;
}
//
// Give the formula to the solver
//
#ifdef PRODUCE_PROOF
bool Cnfizer::giveToSolver ( PTRef f, const ipartitions_t &mask)
#else
bool Cnfizer::giveToSolver ( PTRef f )
#endif
{
    vec<Lit> clause;

    //
    // A unit clause
    //
    if (logic.isLit (f))
    {
        clause.push (theory.findLit (f));
#ifdef PRODUCE_PROOF
        return addClause (clause, mask);
#else
        return addClause (clause);
#endif
    }

    //
    // A clause
    //

    if (logic.isOr (f))
    {
        vec<PTRef> lits;
        retrieveClause (f, lits);

        for (int i = 0; i < lits.size(); i++)
            clause.push (theory.findLit (lits[i]));

#ifdef PRODUCE_PROOF
        return addClause (clause, mask);
#else
        return addClause (clause);
#endif
    }

    //
    // Conjunction
    //
    assert (logic.isAnd (f));
    vec<PTRef> conj;
    retrieveTopLevelFormulae ( f, conj );
    bool result = true;

    for (unsigned i = 0; i < conj.size_( ) && result; i++)
#ifdef PRODUCE_PROOF
        result = giveToSolver (conj[i], mask);

#else
        result = giveToSolver (conj[i]);
#endif
    return result;
}

//
// Retrieve the formulae at the top-level.  Ignore duplicates
//
void Cnfizer::retrieveTopLevelFormulae (PTRef root, vec<PTRef> &top_level_formulae)
{
    vec<PTRef> to_process;

    Map<PTRef, bool, PTRefHash> seen;

    to_process.push (root);

    while (to_process.size() != 0)
    {
        PTRef f = to_process.last();
        to_process.pop();
        Pterm &cand_t = logic.getPterm (f);

        if (logic.isAnd (f))
            for (int i = cand_t.size() - 1; i >= 0; i--) {
                to_process.push (cand_t[i]);
#ifdef PRODUCE_PROOF
            if (logic.hasOriginalAssertion(f))
                    logic.setOriginalAssertion(cand_t[i], logic.getOriginalAssertion(f));
            else if (logic.isAssertion(f))
                    logic.setOriginalAssertion(cand_t[i], f);
#endif
            }
        else if (!seen.has (f))
        {
            top_level_formulae.push (f);
            seen.insert (f, true);
        }
    }
}

//
// Retrieve a clause
//
void Cnfizer::retrieveClause ( PTRef f, vec<PTRef> &clause )
{
    assert (logic.isLit (f) || logic.isOr (f));

    if ( logic.isLit (f) )
        clause.push (f);
    else if ( logic.isOr (f) )
    {
        Pterm &t = logic.getPterm (f);

        for ( int i = 0; i < t.size(); i++)
            retrieveClause ( t[i], clause );
    }
}

//
// Retrieve conjuncts
//
void Cnfizer::retrieveConjuncts ( PTRef f, vec<PTRef> &conjuncts )
{
    assert (logic.isLit (f) || logic.isAnd (f));

    if (logic.isLit (f))
        conjuncts.push (f);
    else
    {
        Pterm &t = logic.getPterm (f);

        for (int i = 0; i < t.size(); i++)
            retrieveConjuncts (t[i], conjuncts);
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


vec<ValPair> *Cnfizer::getModel()
{
    assert (solver.okay());
    vec<lbool> &model = solver.model;
    vec<ValPair> *out = new vec<ValPair>();

    for (Var v = 0; v < model.size(); v++)
    {
        if (logic.isTheoryTerm (tmap.varToPTRef (v)))
            out->push (ValPair (tmap.varToPTRef (v), model[v] == l_True ? "true" : (model[v] == l_False ? "false" : "unknown") ));
    }

    return out;
}

lbool Cnfizer::getTermValue (PTRef tr) const
{
    assert (solver.okay());
    vec<lbool> &model = solver.model;
    PTRef p;
    bool sgn;
    tmap.getTerm (tr, p, sgn);

    if (logic.getPterm (p).getVar() != var_Undef)
    {
        Var v = logic.getPterm (p).getVar();
        lbool val = model[v];
        assert (val != l_Undef);
        return sgn == false ? val : (val == l_True ? l_False : l_True);
    }
    else return l_Undef;
}

// Assumes that the root of the tree is the last element of term_list
PTRef Cnfizer::expandItes (vec<PtChild> &term_list)
{
    assert (term_list.size() > 0);
    vec<PtPair> ites;
    int l = term_list.size() - 1;
    assert (!logic.isTheoryTerm (term_list[l].tr) or !logic.isIte (logic.getPterm (term_list[l].tr).symb()));

    for (int i = 0; i < term_list.size() - 1; i++)
    {
        PtChild ptc   = term_list[i];
        Pterm &parent = logic.getPterm (ptc.parent);
        PTRef tr      = ptc.tr;
        int pos       = ptc.pos;
        Pterm &pt     = logic.getPterm (tr);

        if (logic.isTheoryTerm (tr) and logic.isIte (pt.symb()))
        {
            // (1) Add a new term o_ite with no arguments and same sort as pt
            // (2) add tr to ites
            // (3) replace parent[pos] with o_ite
            SRef sr = logic.getSym (pt.symb()).rsort();
            char *name;
            asprintf (&name, ".oite%d", logic.getPterm (tr).getId());
            PTRef o_ite = logic.mkVar (sr, name);
            // The old term goes to PtPair
            ites.push (PtPair (tr, o_ite));
#ifdef PEDANTIC_DEBUG
            cerr << "Added the term " << logic.printTerm (tr) << " to later processing" << endl;
            cerr << "; changing " << logic.printTerm (parent[pos]) << " to ";
#endif
            parent[pos] = o_ite;
#ifdef PEDANTIC_DEBUG
            cerr << logic.printTerm (parent[pos]) << endl;
#endif
        }
    }

    vec<PTRef> ite_roots;
    ite_roots.push (term_list[l].tr);

    for (int j = 0; j < ites.size(); j++)
    {
        PTRef ite  = ites[j].x;
        PTRef sbst = ites[j].y;
        PTRef b = logic.getPterm (ite)[0];
        PTRef t = logic.getPterm (ite)[1];
        PTRef e = logic.getPterm (ite)[2];

        // b -> (= sbst t)
        vec<PTRef> args_eq;
        args_eq.push (sbst);
        args_eq.push (t);
        PTRef eq_term = logic.mkEq (args_eq);
        assert (eq_term != PTRef_Undef);
        vec<PTRef> args_impl;
        args_impl.push (b);
        args_impl.push (eq_term);
        PTRef if_term = logic.mkImpl (args_impl);
        assert (if_term != PTRef_Undef);
        // \neg b -> (= sbst e)
        vec<PTRef> args_eq2;
        args_eq2.push (sbst);
        args_eq2.push (e);
        PTRef eq_term2 = logic.mkEq (args_eq2);
        assert (eq_term2 != PTRef_Undef);
        PTRef neg_term = logic.mkNot (b);
        vec<PTRef> args_impl2;
        args_impl2.push (neg_term);
        args_impl2.push (eq_term2);

        PTRef else_term = logic.mkImpl (args_impl2);
        assert (else_term != PTRef_Undef);

        ite_roots.push (if_term);
        ite_roots.push (else_term);
    }

    if (ite_roots.size() > 1)
        return logic.mkAnd (ite_roots);
    else return term_list[l].tr;
}

void Cnfizer::getVarMapping (CnfState &cs)
{
    // The mapping to terms
#ifdef VERBOSE_FOPS
    char *out = (char *)malloc (1);
    out[0] = 0;
    char *old;
#endif

    for (int i = 0; i < solver.nVars(); i++)
    {
        PTRef tr = tmap.varToPTRef (i);
        cs.addToMap ({i, tr});
#ifdef VERBOSE_FOPS
        old = out;
        char *map_s;
        char *term_s = logic.printTerm (tmap.varToPTRef (i));
        asprintf (&map_s, "%d -> %d [%s]", i, tmap.varToPTRef (i).x, term_s);
        free (term_s);
        asprintf (&out, "%s%s\n", old, map_s);
        free (map_s);
#endif
    }

#ifdef VERBOSE_FOPS
    cerr << "Cnf looks like" << endl;
    cerr << cs.getCnf() << endl;
    cerr << "Map looks like " << endl;
    cerr << out << endl;
    free (out);
#endif
}
