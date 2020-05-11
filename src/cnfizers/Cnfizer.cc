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
#include "SimpSMTSolver.h"

#include <queue>

using namespace std;

Cnfizer::Cnfizer ( SMTConfig       &config_
                   , Logic         &logic_
                   , TermMapper    &tmap
                   , SimpSMTSolver &solver_
                 ) :
      solver   (solver_)
    , config   (config_  )
    , logic    (logic_)
    , tmap     (tmap)
    , s_empty  (true)
{
    frame_terms.push(logic.getTerm_true()); // frame 0 does not have a var
    frame_term = frame_terms[0];
}

void Cnfizer::initialize()
{
    // TODO: MB: why is all this initialization necessary?
    currentPartition = 0;
    vec<Lit> c;
    Lit l = this->getOrCreateLiteralFor (logic.getTerm_true());
    c.push (l);
    addClause(c);
    c.pop();
    l = this->getOrCreateLiteralFor (logic.getTerm_false());
    c.push (~l);
    addClause(c);
    currentPartition = -1;
}

lbool
Cnfizer::solve(vec<FrameId>& en_frames)
{
    vec<Lit> assumps;
    // Initialize so that by default frames are disabled
    for (int i = 0; i < frame_terms.size(); i++)
        assumps.push(this->getOrCreateLiteralFor(frame_terms[i]));

    // Enable the terms which are listed in en_frames
    // At this point assumps has the same size as frame_terms and the
    // elements are in the same order.  We simply invert the
    // corresponding literals
    for (int i = 0; i < en_frames.size(); i++) {
        int asmp_idx = en_frames[i].id;
        assumps[asmp_idx] = ~assumps[asmp_idx];
    }
    // Filter out the lit_Trues and lit_Falses used as empty values
    Lit lit_true = this->getOrCreateLiteralFor(logic.getTerm_true());
    int i, j;
    for (i = j = 0; i < assumps.size(); i++) {
        if (assumps[i] != lit_true && assumps[i] != ~lit_true)
            assumps[j++] = assumps[i];
    }
    assumps.shrink(i-j);
    return solver.solve(assumps, !config.isIncremental(), config.isIncremental());

}

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
    while (static_cast<unsigned int>(frame_terms.size()) <= frame_id.id) {
        frame_terms.push(logic.getTerm_true());
    }
    // frame_id == {0} is for the bottom frame and we don't want to add
    // literals to it since it is never retracted.
    if (frame_id != FrameId_bottom && frame_terms[frame_id.id] == logic.getTerm_true()) {
        std::string name {Logic::s_framev_prefix};
        name += std::to_string(frame_id.id);
        PTRef frame_term = logic.mkBoolVar(name.c_str());
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

    if (!solver.isOK()) return l_False;

    assert ( formula != PTRef_Undef);

#ifdef PEDANTIC_DEBUG
    cerr << "cnfizerAndGiveToSolver: " << logic.printTerm (formula) << endl;
#endif

#ifdef PRODUCE_PROOF
    assert(logic.getPartitionIndex(formula) != -1);
    currentPartition = logic.getPartitionIndex(formula);
#endif // PRODUCE_PROOF
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
        if (alreadyAsserted.contains(f, frame_term)) {
            continue;
        }
#ifdef PEDANTIC_DEBUG
        cerr << "Adding clause " << logic.printTerm (f) << endl;
#endif
        // Give it to the solver if already in CNF
        if (checkCnf (f) == true || checkClause (f) == true)
        {
#ifdef PEDANTIC_DEBUG
            cerr << " => Already in CNF" << endl;
#endif
            res = giveToSolver (f);
        }

        // Check whether it can be rewritten using deMorgan laws

        else if (checkDeMorgan (f) == true)
        {
#ifdef PEDANTIC_DEBUG
            cout << " => Will be de Morganized" << endl;
#endif
            res = deMorganize (f);
        }
        else
        {
#ifdef PEDANTIC_DEBUG
            cout << " => proper cnfization" << endl;
#endif // PEDANTIC_DEBUG
            res = cnfizeAndAssert (f); // Perform actual cnfization (implemented in subclasses)
        }
        alreadyAsserted.insert(f, frame_term);
    }
    s_empty = false; // solver no longer empty
    if (res) {
        vec<PTRef> nestedBoolRoots = getNestedBoolRoots(formula);
        for (int i = 0; i < nestedBoolRoots.size(); ++i) {
            res &= cnfize(nestedBoolRoots[i]); // cnfize the formula without asserting the top level
        }
        assert(res);
        declareVars(logic.propFormulasAppearingInUF);
    }

    currentPartition = -1;
    return res == false ? l_False : l_Undef;
}

bool Cnfizer::cnfizeAndAssert(PTRef formula) {
    assert(formula != PTRef_Undef);
    // Top level formula must not be and anymore
    assert(!logic.isAnd(formula));
    bool res = true;
    // Add the top level literal as a unit to solver.
    vec<Lit> clause;
    clause.push(this->getOrCreateLiteralFor(formula));
    res &= addClause(clause);

    res &= cnfize(formula);
    return res;
}

void Cnfizer::declareVars(vec<PTRef>& vars)
{
    for (int i = 0; i < vars.size(); i++) {
        Lit l = tmap.getOrCreateLit(vars[i]);
        solver.addVar(var(l));
    }
}

//
// Apply simple de Morgan laws to the formula
//

bool Cnfizer::deMorganize ( PTRef formula )
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
            clause.push (~this->getOrCreateLiteralFor (conjuncts[i]));
#ifdef PEDANTIC_DEBUG
            cerr << "(not " << logic.printTerm (conjuncts[i]) << ")" << endl;
#endif
        }

        rval = addClause(clause);
    }

    return rval;
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

bool Cnfizer::addClause(const vec<Lit> & c_in)
{
    vec<Lit> c;
    c_in.copyTo(c);
    if (frame_term != logic.getTerm_true()) {
        Lit l = this->getOrCreateLiteralFor(frame_term);
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
    std::pair<CRef,CRef> iorefs = std::make_pair(CRef_Undef,CRef_Undef);
    bool res = solver.addOriginalSMTClause(c, iorefs);
    CRef ref = iorefs.first;
    if (ref != CRef_Undef) {
        ipartitions_t parts = 0;
        assert(currentPartition != -1);
        setbit(parts, static_cast<unsigned int>(currentPartition));
        logic.addClauseClassMask(ref, parts);
        for (int i = 0; i < c.size(); ++i) {
            logic.addVarClassMask(var(c[i]), parts);
        }
    }
#else
    bool res = solver.addOriginalSMTClause(c);
#endif
    return res;
}
//
// Give the formula to the solver
//

bool Cnfizer::giveToSolver ( PTRef f )
{
    vec<Lit> clause;

    //
    // A unit clause
    //
    if (logic.isLit (f))
    {
        clause.push (this->getOrCreateLiteralFor (f));
        return addClause(clause);
    }

    //
    // A clause
    //

    if (logic.isOr (f))
    {
        vec<PTRef> lits;
        retrieveClause (f, lits);

        for (int i = 0; i < lits.size(); i++)
            clause.push (this->getOrCreateLiteralFor (lits[i]));

        return addClause(clause);
    }

    //
    // Conjunction
    //
    assert (logic.isAnd (f));
    vec<PTRef> conj;
    retrieveTopLevelFormulae ( f, conj );
    bool result = true;

    for (unsigned i = 0; i < conj.size_( ) && result; i++)
        result = giveToSolver (conj[i]);
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
        Pterm const &t = logic.getPterm (f);

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


lbool Cnfizer::getTermValue (PTRef tr) const
{
    assert (solver.isOK());
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

bool Cnfizer::Cache::contains(PTRef term, PTRef frame_term) {
    return this->cache.find(std::make_pair<>(term, frame_term)) != this->cache.end();
}

void Cnfizer::Cache::insert(PTRef term, PTRef frame_term) {
    assert(!contains(term, frame_term));
    this->cache.insert(std::make_pair<>(term, frame_term));
}
