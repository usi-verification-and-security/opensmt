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
    vec<TSolver*>  solverSchedule;
protected:
    SMTConfig     &config;
    TSolverHandler(SMTConfig & c) : config(c) { }
    void setSolverSchedule(vec<TSolver*> && schedule) { solverSchedule = std::move(schedule); }
public:
    using ItpColorMap = std::map<PTRef, icolor_t>;

    virtual ~TSolverHandler();

    virtual void reset(); // Clear the solver state
    virtual bool verifyFullyBacktracked() const;

    virtual       Logic& getLogic() = 0;
    virtual const Logic& getLogic() const = 0;
    virtual PTRef getInterpolant(const ipartitions_t& mask, ItpColorMap *, PartitionManager& pmanager) = 0;

    void    computeModel      ();                      // Computes a model in the solver if necessary
    bool    assertLit         (PtAsgn);                // Push the assignment to all theory solvers
    void    informNewSplit(PTRef);                     // Recompute split datastructures
    virtual void declareAtom(PTRef tr);                     // Declare atom to the appropriate solver
    virtual lbool getPolaritySuggestion(PTRef) const { return l_Undef; }
    virtual TRes    check(bool);
    virtual vec<PTRef> getSplitClauses();
    virtual void fillTheoryFunctions(ModelBuilder & modelBuilder) const;
private:
    // Helper method for computing reasons
    TSolver* getReasoningSolverFor(PTRef ptref) const;
};
#endif
