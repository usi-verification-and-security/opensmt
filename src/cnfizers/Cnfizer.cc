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

#include <common/InternalException.h>
#include <common/TreeOps.h>
#include <smtsolvers/SimpSMTSolver.h>

#ifdef PEDANTIC_DEBUG
#define TRACE(x) std::cerr << x << std::endl;
#define TRACE_FLA_VEC(v)                                                                                               \
    for (unsigned i = 0; i < v.size_(); ++i)                                                                           \
        std::cerr << i << ": " << logic.termToSMT2String(v[i]) << '\n';                                                \
    std::cerr << std::endl;
#else
#define TRACE(x)
#define TRACE_FLA_VEC(v)
#endif // PEDANTIC_DEBUG

namespace opensmt {
Cnfizer::Cnfizer(Logic & logic, TermMapper & tmap) : logic(logic), tmap(tmap) {}

// Main Routine. Examine formula and give it to the solver
void Cnfizer::cnfize(PTRef formula, FrameId frame_id) {
    currentFrameId = frame_id;
    assert(formula != PTRef_Undef and logic.getSortRef(formula) == logic.getSort_bool());
    TRACE("cnfizerAndGiveToSolver: " << logic.termToSMT2String(formula))

    vec<PTRef> top_level_formulae = topLevelConjuncts(logic, formula);
    assert(top_level_formulae.size() != 0);
    TRACE("Top level formulae:")
    TRACE_FLA_VEC(top_level_formulae)

    // For each top-level conjunct
    for (PTRef topLevelConjunct : top_level_formulae) {
        assert(
            not logic.isAnd(topLevelConjunct)); // Conjunction should have been split when retrieving top-level formulae
        if (alreadyProcessed.contains(topLevelConjunct, frame_id)) { continue; }
        TRACE("Adding clause " << logic.termToSMT2String(f))
        // Give it to the solver if already in CNF
        if (isClause(topLevelConjunct)) {
            TRACE(" => Already a clause")
            processClause(topLevelConjunct);
        } else if (checkDeMorgan(topLevelConjunct)) {
            // Check whether it can be rewritten using deMorgan laws
            TRACE(" => Will be de Morganized")
            deMorganize(topLevelConjunct);
        } else {
            TRACE(" => proper cnfization")
            cnfizeAndAssert(topLevelConjunct); // Perform actual cnfization (implemented in subclasses)
        }
        alreadyProcessed.insert(topLevelConjunct, frame_id);
    }
    vec<PTRef> nestedBoolRoots = logic.getNestedBoolRoots(formula);
    for (PTRef tr : nestedBoolRoots) {
        cnfize(tr); // cnfize the formula without asserting the top level
    }
}

void Cnfizer::cnfizeAndAssert(PTRef formula) {
    assert(formula != PTRef_Undef and not logic.isAnd(formula));
    // Add the top level literal as a unit to solver.
    addClause({this->getOrCreateLiteralFor(formula)});
    cnfize(formula);
}

// Apply simple de Morgan laws to the formula
void Cnfizer::deMorganize(PTRef formula) {
    assert(logic.isNot(formula));
    Pterm const & term = logic.getPterm(formula);
    assert(logic.isAnd(term[0]));
    vec<PTRef> conjuncts;
    vec<Lit> clause;
    retrieveConjuncts(term[0], conjuncts);
    for (PTRef tr : conjuncts) {
        clause.push(~this->getOrCreateLiteralFor(tr));
        TRACE("(not " << logic.termToSMT2String(tr) << ")")
    }
    addClause(std::move(clause));
}

//
// Check whether a formula is a clause
//
bool Cnfizer::isClause(PTRef e) {
    assert(e != PTRef_Undef);
    if (isLiteral(e)) { // Single literals count as clauses
        return true;
    }
    if (not logic.isOr(e)) { return false; }
    vec<PTRef> to_process;
    to_process.push(e);
    while (to_process.size() != 0) {
        PTRef current = to_process.last();
        to_process.pop();
        for (PTRef child : logic.getPterm(current)) {
            if (logic.isOr(child)) {
                to_process.push(child);
            } else {
                if (not isLiteral(child)) { return false; }
            }
        }
    }
    return true;
}

// Check if this is a negation of a clause
bool Cnfizer::checkDeMorgan(PTRef e) {
    Pterm const & term = logic.getPterm(e);
    if (not logic.isNot(term.symb())) return false;
    Map<PTRef, bool, PTRefHash> check_cache;
    return checkPureConj(term[0], check_cache);
}

// Check whether it is a pure conjunction of literals
bool Cnfizer::checkPureConj(PTRef e, Map<PTRef, bool, PTRefHash> & check_cache) {
    if (check_cache.has(e)) return true;
    if (not logic.isAnd(e)) return false;

    vec<PTRef> to_process;
    to_process.push(e);
    while (to_process.size() != 0) {
        PTRef current = to_process.last();
        to_process.pop();

        if (logic.isAnd(current)) {
            for (PTRef tr : logic.getPterm(current)) {
                to_process.push(tr);
            }
        } else if (not isLiteral(current)) {
            return false;
        }
        check_cache.insert(current, true);
    }
    return true;
}

void Cnfizer::addClause(vec<Lit> && clause) {
    (*clauseCallBack)(std::move(clause));
}

void Cnfizer::processClause(PTRef f) {
    if (isLiteral(f)) {
        addClause({getOrCreateLiteralFor(f)});
        return;
    }
    if (logic.isOr(f)) {
        vec<Lit> lits;
        retrieveClause(f, lits);
        addClause(std::move(lits));
        return;
    }
    throw InternalException("UNREACHABLE: Unexpected situation in Cnfizer");
}

void Cnfizer::retrieveClause(PTRef f, vec<Lit> & clause) {
    assert(isLiteral(f) or logic.isOr(f));
    if (isLiteral(f)) {
        clause.push(getOrCreateLiteralFor(f));
    } else if (logic.isOr(f)) {
        Pterm const & t = logic.getPterm(f);
        for (PTRef tr : t) {
            retrieveClause(tr, clause);
        }
    }
}

void Cnfizer::retrieveConjuncts(PTRef f, vec<PTRef> & conjuncts) {
    assert(isLiteral(f) or logic.isAnd(f));
    if (isLiteral(f)) {
        conjuncts.push(f);
    } else {
        Pterm const & t = logic.getPterm(f);
        for (PTRef tr : t) {
            retrieveConjuncts(tr, conjuncts);
        }
    }
}

bool Cnfizer::Cache::contains(PTRef term, FrameId frame) {
    return cache.find({term, frame}) != cache.end() or
           (frame != baseFrame and cache.find({term, baseFrame}) != cache.end());
}

void Cnfizer::Cache::insert(PTRef term, FrameId frame) {
    assert(!contains(term, frame));
    cache.insert({term, frame});
}

// TODO: Fix isAtom!!! (everything that is not a boolean connective should be considered as atom
bool Cnfizer::isLiteral(PTRef ptr) const {
    return (logic.isNot(ptr) and logic.isAtom(logic.getPterm(ptr)[0])) or logic.isAtom(ptr);
}
} // namespace opensmt
