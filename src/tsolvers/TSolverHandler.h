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


#include "PartitionManager.h"
#include "Deductions.h"
#include "TermMapper.h"
#include "TSolver.h"

class TheoryInterpolator;

class THandler;
class TSolver;
class ModelBuilder;

class TSolverHandler
{
    friend THandler;
protected:
    SMTConfig     &config;
protected:
    vec<int>       solverSchedule;   // Why is this here and not in THandler?
    vec<TSolver*>  tsolvers;         // List of ordinary theory solvers

    Map<PTRef,PtAsgn,PTRefHash> substs;

    TSolverHandler(SMTConfig & c)
        : config(c)
    {
        for (int i = 0; i < SolverDescr::getSolverList().size(); i++) {
            SolverDescr* sd = SolverDescr::getSolverList()[i];
            SolverId id = (SolverId)(*sd);
            while (id.id >= (unsigned)tsolvers.size()) tsolvers.push(nullptr);
        }
    }
public:
    virtual ~TSolverHandler();

    virtual void clearSolver(); // Clear the solver state

    virtual       Logic& getLogic() = 0;
    virtual const Logic& getLogic() const = 0;
    virtual PTRef getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t>*, PartitionManager& pmanager) = 0;

    void    setSubstitutions(Map<PTRef,PtAsgn,PTRefHash>& substs_) { substs_.moveTo(substs); }
    Map<PTRef,PtAsgn,PTRefHash> const & getSubstitutions() const { return substs; }


    // DEPRECATED
    ValPair getValue          (PTRef tr) const;

    void    fillTheoryVars    (ModelBuilder& modelBuilder) const;
    void    computeModel      ();                      // Computes a model in the solver if necessary
    bool    assertLit         (PtAsgn);                // Push the assignment to all theory solvers
    void    declareAtoms      (PTRef);                 // Declare atoms to theory solvers
    void    informNewSplit(PTRef);                     // Recompute split datastructures
    void    declareAtom(PTRef tr);                     // Declare atom to the appropriate solver
//    virtual SolverId getId() const { return my_id; }
    virtual lbool getPolaritySuggestion(PTRef) const { return l_Undef; }
    TRes    check(bool);
private:
    // Helper method for computing reasons
    TSolver* getReasoningSolverFor(PTRef ptref) const;
};
#endif
