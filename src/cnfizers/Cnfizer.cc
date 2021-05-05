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
#include "TreeOps.h"
#include "OsmtInternalException.h"

#include <queue>

#ifdef PEDANTIC_DEBUG
#define TRACE(x) std::cerr << x << std::endl;
#define TRACE_FLA_VEC(v)    for (unsigned i = 0; i < v.size_(); ++i) \
                                std::cerr << i << ": " << logic.printTerm(v[i]) << '\n'; \
                            std::cerr << std::endl;
#else
#define TRACE(x)
#define TRACE_FLA_VEC(v)
#endif // PEDANTIC_DEBUG

using namespace std;

Cnfizer::Cnfizer ( SMTConfig       &config_
                   , Logic         &logic_
                   , PartitionManager &pmanager_
                   , TermMapper    &tmap
                   , SimpSMTSolver &solver_
                 ) :
      solver   (solver_)
    , config   (config_  )
    , logic    (logic_)
    , pmanager (pmanager_)
    , tmap     (tmap)
    , s_empty  (true)
    , alreadyAsserted(logic.getTerm_true())
    , frame_terms({logic.getTerm_true()}) // Frame 0 does not have an enabling var
    , current_frame_term(frame_terms[0])
{ }

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
    for (PTRef tr : frame_terms) {
        assumps.push(this->getOrCreateLiteralFor(tr));
    }

    // Enable the terms which are listed in en_frames
    // At this point assumps has the same size as frame_terms and the
    // elements are in the same order.  We simply invert the
    // corresponding literals
    for (const FrameId & fid : en_frames) {
        assumps[fid.id] = ~assumps[fid.id];
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

    current_frame_term = frame_terms[frame_id.id];
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
    TRACE("cnfizerAndGiveToSolver: " << logic.printTerm (formula))

    if (keepPartitionInfo()) {
        assert(pmanager.getPartitionIndex(formula) != -1);
        currentPartition = pmanager.getPartitionIndex(formula);
    }
    // Retrieve top-level formulae - this is a list constructed from a conjunction
    vec<PTRef> top_level_formulae = topLevelConjuncts(logic, formula);
    assert (top_level_formulae.size() != 0);
    TRACE("Top level formulae:")
    TRACE_FLA_VEC(top_level_formulae)
    bool res = true;

    // For each top-level conjunct
    for (unsigned i = 0 ; i < top_level_formulae.size_() && (res == true) ; i ++)
    {
        PTRef f = top_level_formulae[i];
        assert(not logic.isAnd(f)); // Conjunction should have been split when retrieving top-level formulae
        if (alreadyAsserted.contains(f, current_frame_term)) {
            continue;
        }
        TRACE("Adding clause " << logic.printTerm (f))
        // Give it to the solver if already in CNF
        if (isClause(f)) {
            TRACE(" => Already a clause")
            res = assertClause(f);
        } else if (checkDeMorgan(f)) {
            // Check whether it can be rewritten using deMorgan laws
            TRACE(" => Will be de Morganized")
            res = deMorganize (f);
        } else {
            TRACE(" => proper cnfization")
            res = cnfizeAndAssert (f); // Perform actual cnfization (implemented in subclasses)
        }
        alreadyAsserted.insert(f, current_frame_term);
    }
    s_empty = false; // solver no longer empty
    if (res) {
        vec<PTRef> nestedBoolRoots = getNestedBoolRoots(formula);
        for (PTRef tr : nestedBoolRoots) {
            res &= cnfize(tr); // cnfize the formula without asserting the top level
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
    for (PTRef tr : vars) {
        Lit l = tmap.getOrCreateLit(tr);
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

        for (PTRef tr : conjuncts) {
            clause.push (~this->getOrCreateLiteralFor(tr));
            TRACE("(not " << logic.printTerm (tr) << ")")
        }

        rval = addClause(clause);
    }

    return rval;
}



//
// Check whether a formula is in cnf
//

bool Cnfizer::isCnf(PTRef e) {
    return isConjunctionOfClauses(e);
}



bool Cnfizer::isConjunctionOfClauses(PTRef e) {
    if (isClause(e)) { // Single clause counts as a conjunction of clauses
        return true;
    }
    if (not logic.isAnd(e)) {
        return false;
    }
    vec<PTRef> to_process;
    to_process.push (e);

    while (to_process.size() != 0) {
        e = to_process.last();
        to_process.pop();

        Pterm const & and_t = logic.getPterm(e);

        for (PTRef tr : and_t) {
            if (logic.isAnd(tr)) {
                to_process.push(tr);
            } else if (not isClause(tr)) {
                return false;
            }
        }
    }
    return true;
}


//
// Check whether a formula is a clause
//
bool Cnfizer::isClause(PTRef e) {
    assert (e != PTRef_Undef);

    if (isLiteral(e)) { // Single literals count as clauses
        return true;
    }

    if (not logic.isOr(e)) {
        return false;
    }

    vec<PTRef> to_process;

    to_process.push (e);

    while (to_process.size() != 0) {
        e = to_process.last();
        to_process.pop();

        Pterm const & or_t = logic.getPterm (e);

        for (PTRef tr : or_t) {
            if (logic.isOr(tr)) {
                to_process.push(tr);
            } else {
                if (not isLiteral(tr)) {
                    return false;
                }
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
    const Pterm &not_t = logic.getPterm (e);

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

        if (logic.isAnd(e)) {
            for (PTRef tr : and_t) {
                to_process.push(tr);
            }
        } else if (not isLiteral(e)) {
            return false;
        }
        check_cache.insert (e, true);
    }

    return true;
}

bool Cnfizer::addClause(const vec<Lit> & c_in)
{
    vec<Lit> c;
    c_in.copyTo(c);
    if (current_frame_term != logic.getTerm_true()) {
        Lit l = this->getOrCreateLiteralFor(current_frame_term);
        tmap.setFrozen(var(l));
        c.push(l);
    }

    opensmt::pair<CRef, CRef> iorefs{CRef_Undef, CRef_Undef};
    bool res = solver.addOriginalSMTClause(c, iorefs);
    if (keepPartitionInfo()) {
        CRef ref = iorefs.first;
        if (ref != CRef_Undef) {
            ipartitions_t parts = 0;
            assert(currentPartition != -1);
            setbit(parts, static_cast<unsigned int>(currentPartition));
            pmanager.addClauseClassMask(ref, parts);
        }
    }
    return res;
}
//
// Give the formula to the solver
//

bool Cnfizer::assertClause (PTRef f)
{
    vec<Lit> clause;

    //
    // A unit clause
    //
    if (isLiteral(f)) {
        clause.push(this->getOrCreateLiteralFor(f));
        return addClause(clause);
    }

    //
    // A clause
    //

    if (logic.isOr(f)) {
        vec<PTRef> lits;
        retrieveClause (f, lits);

        for (PTRef tr : lits)
            clause.push(this->getOrCreateLiteralFor(tr));

        return addClause(clause);
    }
    throw OsmtInternalException("UNREACHABLE: Unexpected situation in Cnfizer");
}

//
// Retrieve a clause
//
void Cnfizer::retrieveClause ( PTRef f, vec<PTRef> &clause )
{
    assert (isLiteral(f) || logic.isOr (f));

    if (isLiteral(f)) {
        clause.push(f);
    } else if ( logic.isOr (f) ) {
        Pterm const &t = logic.getPterm (f);
        for (PTRef tr : t) {
            retrieveClause(tr, clause);
        }
    }
}

//
// Retrieve conjuncts
//
void Cnfizer::retrieveConjuncts ( PTRef f, vec<PTRef> &conjuncts )
{
    assert (isLiteral(f) || logic.isAnd (f));

    if (isLiteral(f)) {
        conjuncts.push(f);
    } else {
        Pterm &t = logic.getPterm (f);

        for (PTRef tr : t) {
            retrieveConjuncts(tr, conjuncts);
        }
    }
}


lbool Cnfizer::getTermValue (PTRef tr) const
{
    assert (solver.isOK());
    if (tmap.hasLit(tr)) {
        Lit l = tmap.getLit(tr);
        lbool val = solver.modelValue(l);
        assert (val != l_Undef);
        return val;
    }
    else return l_Undef;
}

bool Cnfizer::Cache::contains(PTRef term, PTRef frame_term) {
    return cache.find(std::make_pair<>(term, frame_term)) != cache.end()
        || ( frame_term != zeroLevelTerm && cache.find(std::make_pair<>(term, zeroLevelTerm)) != cache.end());
}

void Cnfizer::Cache::insert(PTRef term, PTRef frame_term) {
    assert(!contains(term, frame_term));
    cache.insert(std::make_pair<>(term, frame_term));
}

bool Cnfizer::isLiteral(PTRef ptr) const {
    return (logic.isNot(ptr) and logic.isAtom(logic.getPterm(ptr)[0])) or logic.isAtom(ptr);
}
