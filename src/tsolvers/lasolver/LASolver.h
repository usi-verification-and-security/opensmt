/*
 *  Copyright (c) 2019-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Copyright (c) 2019-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 */

#ifndef LASOLVER_H
#define LASOLVER_H

#include "Timer.h"
#include "ArithLogic.h"

#include "TSolver.h"
#include "LRAModel.h"
#include "Tableau.h"
#include "Polynomial.h"
#include "Simplex.h"
#include "FarkasInterpolator.h"
#include "LAVarMapper.h"

#include <unordered_map>
#include <unordered_set>

class LAVarStore;
class Delta;
class PartitionManager;

class LASolverStats
{
    public:
        int num_vars;
        opensmt::OSMTTimeVal timer;

        LASolverStats() : num_vars(0) {}

        void printStatistics(std::ostream& os) {
            os << "; Number of LA vars........: " << num_vars << '\n';
            os << "; LA time..................: " << timer.getTime() << " s\n";
        }
};


//
// Class to solve Linear Arithmetic theories
//

class LASolver: public TSolver
{

private:
    struct DecEl { PtAsgn asgn; int dl; };

    ArithLogic&          logic;
    LAVarStore           laVarStore;
    LAVarMapper          laVarMapper;
    LABoundStore         boundStore;
    Simplex              simplex;
    vec<PtAsgn>          decision_trace;
    vec<int>             dec_limit;
    vec<DecEl>           int_decisions;

    PtAsgn               popTermBacktrackPoint();
    PtAsgn               popDecisions();
    void                 pushDecision(PtAsgn);
    int                  backtrackLevel();

    std::vector<opensmt::Real> explanationCoefficients;

    vec<PtAsgn>          LABoundRefToLeqAsgn;
    PtAsgn getAsgnByBound(LABoundRef br) const;
    vec<LABoundRefPair>  LeqToLABoundRefPair;
    LABoundRefPair getBoundRefPair(const PTRef leq) const {
        auto index = Idx(logic.getPterm(leq).getId());
        assert(index < LeqToLABoundRefPair.size_());
        return LeqToLABoundRefPair[index];
    }

    // Possible internal states of the solver
    typedef enum
    {
        INIT, INCREMENT, SAT, UNSAT, NEWSPLIT, UNKNOWN, ERROR
    } LASolverStatus;

    LASolverStats laSolverStats;

    void setBound(PTRef leq);
    bool assertBoundOnVar(LVRef it, LABoundRef itBound_ref);

    PTRef getVarPTRef(LVRef v) const {
        return laVarMapper.getVarPTRef(v);
    }

public:

    LASolver(SMTConfig & c, ArithLogic & l);
    LASolver(SolverDescr dls, SMTConfig & c, ArithLogic & l);

    virtual ~LASolver( );                                      // Destructor ;-)

    virtual void printStatistics(std::ostream &) override;

    virtual void clearSolver() override; // Remove all problem specific data from the solver.  Should be called each time the solver is being used after a push or a pop in the incremental interface.

    void getNewSplits(vec<PTRef>& splits) override;
    void  declareAtom        (PTRef tr) override;                // Inform the theory solver about the existence of an atom
    TRes  check              (bool) override;                    // Checks the satisfiability of current constraints
    bool  check_simplex      (bool);
    bool  assertLit          ( PtAsgn ) override;                // Push the constraint into Solver
    void  pushBacktrackPoint ( ) override;                       // Push a backtrack point
    void  popBacktrackPoint  ( ) override;                       // Backtrack to last saved point
    void  popBacktrackPoints ( unsigned int ) override;         // Backtrack given number of saved points
    lbool getPolaritySuggestion(PTRef) const;
    vec<PTRef> collectEqualitiesFor(vec<PTRef> const & vars, std::unordered_set<PTRef, PTRefHash> const & knownEqualities) override;

    PTRef getRealInterpolant(const ipartitions_t &, std::map<PTRef, icolor_t>*, PartitionManager & pmanager);
    PTRef getIntegerInterpolant(std::map<PTRef, icolor_t> const &);

    // Return the conflicting bounds
    void getConflict(vec<PtAsgn> &) override;

    ArithLogic& getLogic() override;
    bool        isValid(PTRef tr) override;


private:

    Map<LVRef, bool, LVRefHash> int_vars_map; // stores problem variables for duplicate check
    vec<LVRef> int_vars;                      // stores the list of problem variables without duplicates
    double seed = 123;

    LABoundStore::BoundInfo addBound(PTRef leq_tr);
    void updateBound(PTRef leq_tr);
    LVRef exprToLVar(PTRef expr); // Ensures this term and all variables in it has corresponding LVAR.  Returns the LAVar for the term.
    void storeExplanation(Simplex::Explanation &&explanationBounds);

    std::unique_ptr<Tableau::Polynomial> expressionToLVarPoly(PTRef term);

    opensmt::Number getNum(PTRef);

    bool isIntVar(LVRef v) { return int_vars_map.has(v); }
    void markVarAsInt(LVRef);

    // Compute the values for an upper bound v ~ c and its negation \neg (v ~ c), where ~ is < if strict and <= if !strict
    LABoundStore::BoundValuePair getBoundsValue(LVRef v, const Real & c, bool strict);
    LABoundStore::BoundValuePair getBoundsValueForIntVar(const Real & c, bool strict);
    LABoundStore::BoundValuePair getBoundsValueForRealVar(const Real & c, bool strict);

    LVRef getLAVar_single(PTRef term);                      // Initialize a new LA var if needed, otherwise return the old var
    bool hasVar(PTRef expr);
    LVRef getVarForLeq(PTRef ref)  const  { return laVarMapper.getVarByLeqId(logic.getPterm(ref).getId()); }
    LVRef getVarForTerm(PTRef ref) const  { return laVarMapper.getVarByPTId(logic.getPterm(ref).getId()); }
    void notifyVar(LVRef);                             // Notify the solver of the existence of the var. This is so that LIA can add it to integer vars list.

    // Random splitting heuristic
    LVRef splitOnRandom(vec<LVRef> const &);
    TRes checkIntegersAndSplit();
    bool isModelInteger (LVRef v) const;
    TRes cutFromProof();
    bool shouldTryCutFromProof() const;

    void getSuggestions( vec<PTRef>& dst, SolverId solver_id );                                   // find possible suggested atoms
    void getSimpleDeductions(LVRef v, LABoundRef);      // find deductions from actual bounds position
    unsigned getIteratorByPTRef( PTRef e, bool );                                                 // find bound iterator by the PTRef
    inline bool getStatus( );                               // Read the status of the solver in lbool
    bool setStatus( LASolverStatus );               // Sets and return status of the solver
    void initSolver( );                                     // Initializes the solver

    void computeConcreteModel(LVRef v, const opensmt::Real& d);
    void computeModel() override;

    std::vector<opensmt::Real> concrete_model;              // Save here the concrete model for the vars indexed by Id

    opensmt::Real evaluateTerm(PTRef tr);

    LASolverStatus status;                  // Internal status of the solver (different from bool)

    void fillTheoryFunctions(ModelBuilder & modelBuilder) const override;

    PTRef interpolateUsingEngine(FarkasInterpolator &) const;

    inline int     verbose                       ( ) const { return config.verbosity(); }

    // Debug stuff
    void isProperLeq(PTRef tr);  // The Leq term conforms to the assumptions of its form.  Only asserts.
    void deduce(LABoundRef bound_prop);
};

#endif
