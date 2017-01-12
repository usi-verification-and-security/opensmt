#ifndef TSolverHandler_H
#define TSolverHandler_H

/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2015 Antti Hyvarinen
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


#include "SMTConfig.h"
#include "Deductions.h"
#include "TSolver.h"
#include "Logic.h"
#include "TreeOps.h"
#include "TermMapper.h"

#ifdef PRODUCE_PROOF
#include "TheoryInterpolator.h"
#endif

class THandler;

class TSolverHandler
{
    friend THandler;
protected:
    SolverId       my_id;
    SMTConfig     &config;
public:
    TermMapper    &tmap;
protected:
    vec<DedElem>  &deductions;
    vec<int>       solverSchedule;   // Why is this here and not in THandler?
    vec<TSolver*>  tsolvers;         // List of ordinary theory solvers

    Map<PTRef,PtAsgn,PTRefHash> substs;

    TSolverHandler(SMTConfig &c, vec<DedElem> &d, Logic& l, TermMapper& tmap)
        : config(c)
        , deductions(d)
        , tmap(tmap)
    {
        for (int i = 0; i < SolverDescr::getSolverList().size(); i++) {
            SolverDescr* sd = SolverDescr::getSolverList()[i];
            SolverId id = (SolverId)(*sd);
            while (id.id >= tsolvers.size()) tsolvers.push(NULL);
        }
    }
public:
    virtual ~TSolverHandler()
    {
        for (int i = 0; i < tsolvers.size(); i++)
            if (tsolvers[i] != NULL) delete tsolvers[i];
    }

    virtual void clearSolver(); // Clear the solver state

    virtual       Logic& getLogic() = 0;
    virtual const Logic& getLogic() const = 0;
#ifdef PRODUCE_PROOF
    virtual TheoryInterpolator* getTheoryInterpolator() = 0;
    virtual PTRef getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t>*) = 0;
#endif

    void    setSubstitutions(Map<PTRef,PtAsgn,PTRefHash>& substs_) { substs_.moveTo(substs); }
    ValPair getValue          (PTRef tr) const;
    void    computeModel      ();                      // Computes a model in the solver if necessary
    bool    assertLit         (PtAsgn);                // Push the assignment to all theory solvers
    virtual bool assertLit_special(PtAsgn) = 0;        // Push the assignnment to the theory solver, with equality splitting if necessary
    void    declareTermTree      (PTRef);                 // Declare the terms in the formula recursively.
    char*   printValue(PTRef tr);
    char*   printExplanation(PTRef tr);
    void    declareTerm(PTRef tr);              // Declare the term to the appropriate solver
    virtual SolverId getId() const { return my_id; }
    virtual void fillTmpDeds(PTRef root, Map<PTRef,int,PTRefHash> &refs) = 0;
    bool check(bool);
};
#endif
