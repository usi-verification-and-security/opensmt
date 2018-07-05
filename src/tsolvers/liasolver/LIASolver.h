#ifndef LIASOLVER_H
#define LIASOLVER_H

//#define GAUSSIAN_DEBUG


#include "LIALogic.h"
#include "LASolver.h"


class LIASolverStats: public LASolverStats  //PS. check all opensmt::real and should I change them to opensmt::integer
{
public:

    int num_vars;
    opensmt::OSMTTimeVal bb_timer;

    LIASolverStats()
            : num_vars(0)
            , LASolverStats()
    {}

    void printStatistics(ostream& os) override
    {
        os << "; -------------------------" << endl;
        os << "; STATISTICS FOR LIA SOLVER" << endl;
        os << "; -------------------------" << endl;
        LASolverStats::printStatistics(os);
        os << "; Number of LIA vars.......: " << num_vars << endl;
        //os << "; Pivot operations.........: " << num_pivot_ops << endl;
        //os << "; Bland operations.........: " << num_bland_ops << endl;
        os << "; BB time.............: " << bb_timer.getTime() << " s\n";
    }
};


//
// Class to solve Linear Arithmetic theories
//

class LIASolver: public LASolver
{
private:

    struct LVRefPair { LVRef p1; LVRef p2; };
//    vector<opensmt::Real*> numbers_pool;    // Collect numbers.  Should work as a simple memory managemet system
    LIALogic&            logic; //PS. shall I declare logic as LIA?

    typedef enum
    {
        INIT, INCREMENT, SAT, UNSAT, ERROR
    } LIASolverStatus;


    LIASolverStats lasolverstats;


public:

    LIASolver(SMTConfig & c, LIALogic& l, vec<DedElem>& d);

    ~LIASolver( );                                      // Destructor ;-)

    virtual void clearSolver() override; // Remove all problem specific data from the solver.  Should be called each time the solver is being used after a push or a pop in the incremental interface.

    LIALogic&  getLogic() override { return logic; }
    bool  check    ( bool complete) override; // Checks the satisfiability of current constraints //PS. add the implementation to LIASolver.C
    void computeConcreteModel(LVRef v) override;
    void computeModel() override;

protected:

private:

    inline bool setStatus( LIASolverStatus );               // Sets and return status of the solver
    void initSolver( );                                     // Initializes the solver

//    void addVarToRow( LVRef, LVRef, opensmt::Real*);
    bool checkIntegersAndSplit();                           //
    bool isModelInteger (LVRef v) const;

    LIASolverStatus status;                  // Internal status of the solver (different from bool)

    opensmt::Integer2 getInt(PTRef r) ;
/*
    // The variable system
    class ModelPoly {
        vec<PolyTermRef> poly;
    public:
        ModelPoly() {}
        ModelPoly(const ModelPoly &o) { o.poly.copyTo(poly); }
        ModelPoly(const vec<PolyTermRef>& v) { v.copyTo(poly); }
        PolyTermRef operator[](int i) const { return poly[i]; }
        void operator=(const ModelPoly &o) { o.poly.copyTo(poly); }
        int size() const { return poly.size(); }
    };
    Map<PTRef,ModelPoly,PTRefHash> removed_by_GaussianElimination;  */     // Stack of variables removed during Gaussian elimination
//    void solveForVar(PolyRef pr, int idx, vec<PolyTermRef>& expr);       // Solve the poly pr for the variable pr[idx] and place the resulting expression to expr

//PS. do I need to have the rest in LIA and LRA solver or having in LASOlver is enough?

/*
    // Two reloaded output operators
    inline friend ostream & operator <<( ostream & out, LIASolver & solver )
    {
        solver.print( out );
        return out;
    }

    inline friend ostream & operator <<( ostream & out, LIASolver * solver )
    {
        solver->print( out );
        return out;
    }
    ValPair getValue(PTRef tr) override;  // Computes the model and changes state.
    inline int     verbose                       ( ) const { return config.verbosity(); }

    // Debug stuff
    char* printValue(PTRef tr) override { char* tmp = (char*)malloc(1); tmp[0] = '\0'; return tmp; } // Implement later...
    char* printExplanation(PTRef tr) override { return printValue(tr); } // Implement later...
    void isProperLeq(PTRef tr);  // The Leq term conforms to the assumptions of its form.  Only asserts.
    char* printVar(LVRef v);
    bool valueConsistent(LVRef v); // Debug: Checks that the value of v in the model is consistent with the evaluated value of the polynomial of v in the same model.
    bool stackOk();
    bool checkConsistency();
    bool checkTableauConsistency();
    bool checkRowConsistency();
    bool checkColumnConsistency();
    void crashInconsistency(LVRef v, int line);*/
};

#endif
