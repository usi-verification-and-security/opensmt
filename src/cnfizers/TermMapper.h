/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

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


#ifndef TERMMAPPER_H
#define TERMMAPPER_H
#include "Map.h"
#include "SolverTypes.h"
#include "PTRef.h"
#include "Logic.h"
class TermMapper {
  private:
    int         var_cnt;
    Logic&      logic;
    vec<bool>   frozen;
    vec<PTRef>  varToTerm; // Mapping Var -> PTRef
    Map<PTRef, Var, PTRefHash> termToVar; // Mapping PTRef -> Var; NOTE: Only positive terms are stored!

    // Given a term computes the positive term and a sign. A -> A, false; (not A) -> A, true
    void getTerm(PTRef tr, PTRef& tr_pos, bool& sgn) const;

    // Given a term returns the positive version of the term.
    PTRef toPositive(PTRef term) const;

    // Giver a term computes the positive term and SAT variable correspoding to the positive term.
    void getVar(PTRef, PTRef&, Var&) const;

    // Check if there exists a SAT variable corresponding to the term. On success fill the output paramter v and returns true.
    bool peekVar(PTRef positiveTerm, Var& v) const;

    // Creates a new bound between the given term and the returned SAT variable. Must not be called multiple times for the same term.
    Var addBinding(PTRef tr);



  public:
    TermMapper(Logic& l) : var_cnt(0), logic(l) {}

    void setFrozen(Var v) { frozen[v] = true; }
    bool isFrozen(Var v)  { return frozen[v]; }


    /*
     * Returns a SAT literal corresponding to the giver BOOLEAN term.
     * If no SAT variable has been assigned to (the positive version of) this term yet, a new one will be created.
     * Handles the sign of the term correctly, i.e., it returned negative literal for negative term and
     * positive literal for positive term.
     */
    const Lit getOrCreateLit(PTRef ptr);

    // Returns the variable corresponding to the term. The connection must already exist.
    Var  getVar(PTRef)    const;
    // Returns the literal corresponding to the term. The connection must already exist.
    Lit  getLit(PTRef)    const;
    // Test if the given term already has an assigned SAT variable
    bool hasLit(PTRef tr) const { return termToVar.has(toPositive(tr)); }

    // Returns the term to which the given variable has been assigned. The connection must already exist.
    PTRef varToPTRef(Var v) const { assert(v >= 0); return varToTerm[v]; }

    int  nVars()          const { return varToTerm.size(); }
};

#endif
