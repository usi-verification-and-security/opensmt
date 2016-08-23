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
#ifndef THEORY_H
#define THEORY_H

#include "Deductions.h"
#include "TermMapper.h"
#include "Logic.h"
#include "LRALogic.h"
#include "LRATHandler.h"
#include "UFTHandler.h"

// Simplification in frames:
// A frame F_i consists of:
//  P_i : a list of asserts given on this frame
//  U_i : the unit clauses, or facts, implied by P_1 /\ ... /\ P_i
//  R_i : P_i simplified with U_1, ..., U_i
//
// We require that U_i \cap U_j = \emptyset
// if U_1 /\ ... /\ U_i is unsatisfiable, then R_i must be false
// R_i must not be simplified with any U_j such that j > i.
//
// Some of the U_i might be theory equalities.  These allow potentially
// more simplifications.  For instance in arithmetics if (= a b) \in U_j,
// a may be substituted everywhere in U_k, j <= k <= i.  These must be
// simplified using a theory specific simplifier.  This will be part of
// the simplifications we do.
//
// The simplification has to use information from the theory solver and
// propositional structure to accomplish this.  The unit clauses need to
// be derived in a closure.  For the closure we need the problem P_i
// separately as input to computeSubstitutions.  Hence the interface
// will be as follows:
//  - units U_1 ... U_{curr-1}
//  - conjunction of simplified problems R_i ... R_{curr-1}
//  - The problem to be simplified P_{curr}
//  - The last frame where the simplified problem R_{curr} and the new
//    unit clauses U_{curr} will be placed
//

struct PushFrame
{
    PushFrame()                                 { id = id_counter; id_counter += 1; }
    int  getId() const                          { return id; }
    int  size()  const                          { return formulas.size(); }
    void push(PTRef tr)                         { formulas.push(tr); }
    PTRef operator[] (int i) const              { return formulas[i]; }
    Map<PTRef,lbool,PTRefHash> units; // Contains the unit (theory) clauses that are implied up to here
    PTRef root;
    void addSeen(PTRef tr)                      { seen.insert(tr, l_True); }
    bool isSeen(PTRef tr)                       { return seen.has(tr); }
 private:
    vec<PTRef> formulas;
    static int id_counter;
    int id;
    //  If a lower frame F contains a substitution x = f(Y), x = f(Y)
    //  needs to be inserted into the root of the lower frame
    Map<PTRef,lbool,PTRefHash> seen; // Contains all the variables x seen in this frame.
};

class Theory
{
  protected:
    vec<DedElem> deductions;
    SMTConfig &  config;
    PTRef getCollateFunction(vec<PushFrame>& formulas, int curr);
  public:
    virtual Logic          &getLogic()              = 0;
    virtual TSolverHandler &getTSolverHandler()     = 0;
    virtual TSolverHandler *getTSolverHandler_new(vec<DedElem>&) = 0;
    virtual bool            simplify(vec<PushFrame>&, int) = 0; // Simplify a vector of PushFrames in an incrementality-aware manner
    vec<DedElem>           &getDeductionVec()   { return deductions; }
    bool                    computeSubstitutions(PTRef coll_f, vec<PushFrame>& frames, int curr);
    Theory(SMTConfig &c) : config(c)            {}
    virtual ~Theory()                           {};
};

class LRATheory : public Theory
{
  private:
    LRALogic    lralogic;
    LRATHandler lratshandler;
  public:
    LRATheory(SMTConfig& c)
        : Theory(c)
        , lralogic(c)
        , lratshandler(c, lralogic, deductions)
    { }
    ~LRATheory() {};
    LRALogic&    getLogic()    { return lralogic; }
    LRATHandler& getTSolverHandler() { return lratshandler; }
    LRATHandler *getTSolverHandler_new(vec<DedElem> &d) { return new LRATHandler(config, lralogic, d); }
    bool simplify(vec<PushFrame>&, int); // Theory specific simplifications
};

class UFTheory : public Theory
{
  private:
    Logic      uflogic;
    UFTHandler tshandler;
  public:
    UFTheory(SMTConfig& c)
        : Theory(c)
        , uflogic(c)
        , tshandler(c, uflogic, deductions)
    {}
    ~UFTheory() {}
    Logic&       getLogic()             { return uflogic; }
    UFTHandler&  getTSolverHandler()    { return tshandler; }
    const UFTHandler& getTSolverHandler() const { return tshandler; }
    UFTHandler *getTSolverHandler_new(vec<DedElem>& d) { return new UFTHandler(config, uflogic, d); }
    bool simplify(vec<PushFrame>&, int);
};

#endif
