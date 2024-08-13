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

#ifndef TSOLVER_H
#define TSOLVER_H

#include "Deductions.h"
#include "TResult.h"

#include <options/SMTConfig.h>
#include <pterms/PtStructs.h>
#include <minisat/core/SolverTypes.h>
#include <minisat/mtl/MapWithKeys.h>

#include <unordered_set>

namespace opensmt {

// forward declaration
class TheoryInterpolator;
class ModelBuilder;
class Logic;
///////////////////////

class TSolverStats
{
  public:
    long sat_calls;
    long unsat_calls;

    TSolverStats ()
    : sat_calls         ( 0 )
    , unsat_calls       ( 0 )
    , conflicts_sent    ( 0 )
    , avg_conf_size     ( 0 )
    , max_conf_size     ( 0 )
    , min_conf_size     ( 32767 )
    , deductions_done   ( 0 )
    , deductions_sent   ( 0 )
    , reasons_sent      ( 0 )
    , avg_reas_size     ( 0 )
    , max_reas_size     ( 0 )
    , min_reas_size     ( 32767 )
    {}

    // Statistics for theory solvers
    void printStatistics ( std::ostream & os )
    {
        os << "; Satisfiable calls........: " << sat_calls << '\n';
        os << "; Unsatisfiable calls......: " << unsat_calls << '\n';
        if ( unsat_calls > 0 )
        {
            os << "; Conflicts sent...........: " << conflicts_sent << '\n';
            if ( conflicts_sent > 0 )
            {
                os << "; Average conflict size....: " << avg_conf_size / (float)conflicts_sent << '\n';
                os << "; Max conflict size........: " << max_conf_size << '\n';
                os << "; Min conflict size........: " << min_conf_size << '\n';
            }
        }
        if ( sat_calls > 0 )
        {
            os << "; Deductions done..........: " << deductions_done << '\n';
            os << "; Deductions sent..........: " << deductions_sent << '\n';
            os << "; Reasons sent.............: " << reasons_sent << '\n';
            if ( reasons_sent > 0 )
            {
                os << "; Average reason size......: " << avg_reas_size / (float)reasons_sent << '\n';
                os << "; Max reason size..........: " << max_reas_size << '\n';
                os << "; Min reason size..........: " << min_reas_size << '\n';
            }
        }
        os << std::flush;
    }

    // Calls statistics
    // Conflict statistics
    int   conflicts_sent;
    float avg_conf_size;
    int   max_conf_size;
    int   min_conf_size;
    // Deductions statistics
    int   deductions_done;
    int   deductions_sent;
    int   reasons_sent;
    float avg_reas_size;
    int   max_reas_size;
    int   min_reas_size;
};



class TSolver
{
private:
    /**
     * Polarity map now merges its original meaning and keeping track of deductions.
     * It keeps track about polarities of theory atoms the solver already knows about.
     * This information can come from two sources:
     * - from SAT solver through assertLit
     * - from TSolver's own deductions
     */
    Map<PTRef,lbool,PTRefHash>  polarityMap;

protected:
    SolverId                    id;              // Solver unique identifier
    vec<PtAsgn>                 explanation;     // Stores the explanation
    vec<PtAsgn_reason>          th_deductions;   // List of deductions computed by the theory
    size_t                      deductions_next; // Index of next deduction to communicate
    vec<size_t>                 deductions_lim;  // Keeps track of deductions done up to a certain point
    vec<size_t>                 deductions_last; // Keeps track of deductions done up to a certain point
    vec<PTRef>                  suggestions;     // List of suggestions for decisions

    TSolverStats                generalTSolverStats;

    // Methods for querying and modifying infromation about known polarities
    void  setPolarity(PTRef tr, lbool p);
    lbool getPolarity(PTRef tr) const    { return polarityMap[tr]; }
    void  clearPolarity(PTRef tr)        { polarityMap[tr] = l_Undef; }
    bool  hasPolarity(PTRef tr) const    { if (polarityMap.has(tr)) { return polarityMap[tr] != l_Undef; } else return false; }

    // Method for storing information about deductions (Derived solvers should use this and not manipulate fields themselves)
    void storeDeduction(PtAsgn_reason ded) {
        th_deductions.push(ded);
        setPolarity(ded.tr, ded.sgn);
    }

    vec<PTRef>                  splitondemand;

public:
    // The states of the TSolver check query


    TSolver(SolverId id_, const char * name_, SMTConfig & c)
    : id(id_)
    , deductions_next(0)
    , has_explanation(false)
    , name(name_)
    , config  (c)
    {}

    virtual ~TSolver () = default;

    // Called after every check-sat.
    virtual void clearSolver();

    virtual bool                assertLit           (PtAsgn) = 0              ;  // Assert a theory literal
    virtual void                pushBacktrackPoint  ( )                       ;  // Push a backtrack point
    virtual void                popBacktrackPoint   ( )                       ;  // Backtrack to last saved point
    virtual void                popBacktrackPoints  ( unsigned int )          ;  // Backtrack given number of points
    virtual TRes                check               ( bool ) = 0              ;  // Check satisfiability
    inline std::string          getName             ( ) { return name; }         // The name of the solver
    virtual void fillTheoryFunctions(ModelBuilder &) const { throw std::logic_error{"Model computation not supported for the used theory yet!"}; }
    virtual void computeModel() = 0;                      // Compute model for variables
    virtual void getConflict(vec<PtAsgn> &) = 0;          // Return conflict
    virtual vec<PtAsgn> getReasonFor(PtAsgn lit);
    virtual bool hasNewSplits();                          // Are there new splits?
    virtual void getNewSplits(vec<PTRef>&);               // Return new splits if any
    virtual PtAsgn_reason getDeduction();                 // Return an implied literal based on the current state
    virtual vec<PTRef> collectEqualitiesFor(vec<PTRef> const &, std::unordered_set<PTRef, PTRefHash> const &) { return {}; }

    SolverId getId() { return id; }
    bool hasExplanation() { return has_explanation; }
    virtual void declareAtom(PTRef tr) = 0;
    virtual void  informNewSplit(PTRef) { };
    virtual Logic& getLogic() = 0;
    virtual bool isValid(PTRef tr) = 0;
    bool isInformed(PTRef tr) const { return informed_PTRefs.has(tr); }

    virtual void printStatistics(std::ostream & os);
protected:
    void                        setInformed(PTRef tr) { informed_PTRefs.insert(tr, true); }
    const vec<PTRef> &          getInformed() { return informed_PTRefs.getKeys(); }
    bool                        has_explanation;  // Does the solver have an explanation (conflict detected)
    std::string                 name;             // Name of the solver
    SMTConfig &                 config;           // Reference to configuration
    vec< size_t >               backtrack_points; // Keeps track of backtrack points

private:
    MapWithKeys<PTRef,bool,PTRefHash>   informed_PTRefs;
};

}

#endif
