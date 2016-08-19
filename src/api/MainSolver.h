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

#ifndef MAINSOLVER_H
#define MAINSOLVER_H

#include "Logic.h"
#include "Theory.h"
#include "SimpSMTSolver.h"
#include "Egraph.h"
#include "Tseitin.h"
#include <thread>
#include <mutex>
#include <random>

class sstat {
    char value;
  public:
    explicit sstat(int v) : value(v) {}
    bool operator == (sstat s) const { return value == s.value; }
    bool operator != (sstat s) const { return value != s.value; }
    sstat() : value(0) {}
    sstat(lbool l) {
        if (l == l_True)
            value = 1;
        else if (l == l_False)
            value = -1;
        else if (l == l_Undef)
            value = 0;
        else assert(false);
    }
    char getValue()            const { return value; }
    friend sstat toSstat(int v);
};

inline sstat toSstat(int v) {return sstat(v); }

const sstat s_True  = toSstat( 1);
const sstat s_False = toSstat(-1);
const sstat s_Undef = toSstat( 0);
const sstat s_Error = toSstat( 2);


class MainSolver
{
  private:
    const static int sz_idx              = 0;
    const static int map_offs_idx        = 1;
    const static int termstore_offs_idx  = 2;
    const static int symstore_offs_idx   = 3;
    const static int idstore_offs_idx    = 4;
    const static int sortstore_offs_idx  = 5;
    const static int logicstore_offs_idx = 6;
    const static int cnf_offs_idx        = 7;

    int compress_buf(const int* buf_in, int*& buf_out, int sz, int& sz_out) const;
    int decompress_buf(int* buf_in, int*& buf_out, int sz, int& sz_out) const;

    class pi {
      public:
        PTRef x;
        bool done;
        pi(PTRef x_) : x(x_), done(false) {}
    };
    Logic&         logic;
    TermMapper&    tmap;
    SMTConfig&     config;
    THandler&      thandler;
    vec<DedElem>   deductions;
    SimpSMTSolver* smt_solver;
    Tseitin        ts;
    vec<PushFrame> formulas;

    int            simplified_until; // The formulas have been simplified up to and including formulas[simplified_until-1].
    sstat          status;           // The status of the last solver call (initially s_Undef)

    bool          binary_init; // Was the formula loaded from .osmt2

    class FContainer {
        PTRef   root;

      public:
              FContainer(PTRef r) : root(r)     {}
        void  setRoot   (PTRef r)               { root = r; }
        PTRef getRoot   ()        const         { return root; }
    };

    void expandItes(FContainer& fc, vec<PtChild>& terms);

    sstat giveToSolver(PTRef root, int push_id) {
        if (ts.cnfizeAndGiveToSolver(root, push_id) == l_False) return s_False;
        return s_Undef; }

    FContainer simplifyEqualities(vec<PtChild>& terms);

    void computeIncomingEdges(PTRef tr, Map<PTRef,int,PTRefHash>& PTRefToIncoming);
    PTRef rewriteMaxArity(PTRef, Map<PTRef,int,PTRefHash>&);
    PTRef mergePTRefArgs(PTRef, Map<PTRef,PTRef,PTRefHash>&, Map<PTRef,int,PTRefHash>&);

    vec<MainSolver*> parallel_solvers;

    FContainer root_instance; // Contains the root of the instance once simplifications are done


  public:
    MainSolver(THandler& thandler, SMTConfig& c, SimpSMTSolver *s )
        : logic(thandler.getLogic())
        , tmap(thandler.getTMap())
        , config(c)
        , status(s_Undef)
        , thandler(thandler)
        , smt_solver(s)
        , ts( config
            , logic
            , tmap
            , thandler
            , *s )
        , binary_init(false)
        , root_instance(logic.getTerm_true())
        , simplified_until(0)
    {
        formulas.push();
        PushFrame& last = formulas.last();
        last.push(logic.getTerm_true());
    }

    ~MainSolver() { }

    SMTConfig& getConfig() { return config; }
    SimpSMTSolver& getSMTSolver() { return *smt_solver; }

    THandler& getTHandler() { return thandler; }
    Logic&    getLogic()    { return thandler.getLogic(); }
    Theory&   getTheory()   { return thandler.getTheory(); }
    sstat push(PTRef root);
    void push();
    bool pop();
    sstat insertFormula(PTRef root, char** msg);

    void initialize() { ts.solver.initialize(); ts.initialize(); }

    sstat simplifyFormulas() { char* msg; sstat res = simplifyFormulas(&msg); if (res == s_Error) { printf("%s\n", msg); } return res; }
    sstat simplifyFormulas(char** err_msg);
    sstat solve           ();
    sstat check           ();      // A wrapper for solve which simplifies the loaded formulas and initializes the solvers


    sstat lookaheadSplit  (int d)  { return status = sstat(ts.solver.lookaheadSplit2(d)); }
    sstat getStatus       ()       { return status; }
    bool  solverEmpty     () const { return ts.solverEmpty(); }
    bool  readSolverState  (const char* file, char** msg);
    bool  readSolverState  (int* buf, int buf_sz, bool compressed, char **msg);
    bool  writeState       (const char* file, CnfState& cs, char** msg);
    bool  writeState       (int* &buf, int &buf_sz, bool compress, CnfState& cs, char** msg);
    bool  writeSolverState (const char* file, char** msg);
    bool  writeSolverState (int* &buf, int &buf_sz, bool compress, char** msg);
    bool  writeSolverState_smtlib2 (const char* file, char** msg);

    void  addToConj(vec<vec<PtAsgn> >& in, vec<PTRef>& out); // Add the contents of in as disjuncts to out
    bool  writeSolverSplits_smtlib2(const char* file, char** msg);
    bool  writeSolverSplits(const char* file, char** msg);
    bool  writeSolverSplit (int s, int* &split, int &split_sz, bool compress, char** msg);
    bool  writeSolverSplits(int** &splits, char** msg);
    void  deserializeSolver(const int* termstore_buf, const int* symstore_buf, const int* idstore_buf, const int* sortstore_buf, const int* logicdata_buf, CnfState& cs);

    // Values
    lbool   getTermValue   (PTRef tr) const { return ts.getTermValue(tr); }
    ValPair getValue       (PTRef tr) const;
    void    getValues      (const vec<PTRef>&, vec<ValPair>&) const;
    bool    getAssignment  (const char*);


    void solve_split(int i,int s, int wpipefd, std::mutex *mtx);
    void stop() { ts.solver.stop = true; }

    bool readFormulaFromFile(const char *file);
};

#endif //
