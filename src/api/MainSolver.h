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


#include "Tseitin.h"
#include "SimpSMTSolver.h"
#include "Model.h"

#include <memory>

class Logic;

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

    class PushFramesWrapper {
    private:
        vec<PFRef> frames;
        std::size_t simplified_until = 0; // The frame have been simplified up to (excluding) frames[simplified_until].
    public:
        PFRef last() const { assert(frames.size() > 0); return frames.last(); }

        std::size_t size() const { return frames.size_(); }

        const vec<PFRef>& getFrameReferences() const { return frames; }

        PFRef getFrameReference(std::size_t i) const { return frames[i]; }

        std::size_t getSimplifiedUntil() const { return simplified_until; }

        void setSimplifiedUntil(std::size_t n) { simplified_until = n; }

        void push(PFRef frame_ref) { frames.push(frame_ref); }

        void pop() {
            frames.pop();
            if (simplified_until > size()) { simplified_until = size(); }
        }

    };


    std::unique_ptr<Theory>         theory;
    TermMapper                      term_mapper;
    THandler                        thandler;
    std::unique_ptr<SimpSMTSolver>  smt_solver;
    Logic&                          logic;
    SMTConfig&                      config;
    PushFrameAllocator&             pfstore;
    Tseitin                         ts;
    PushFramesWrapper               frames;


    opensmt::OSMTTimeVal query_timer; // How much time we spend solving.
    std::string          solver_name; // Name for the solver
    int            check_called;     // A counter on how many times check was called.
    sstat          status;           // The status of the last solver call (initially s_Undef)
    unsigned int   inserted_formulas_count = 0; // Number of formulas that has been inserted to this solver


    bool          binary_init; // Was the formula loaded from .osmt2

    class FContainer {
        PTRef   root;

      public:
              FContainer(PTRef r) : root(r)     {}
        void  setRoot   (PTRef r)               { root = r; }
        PTRef getRoot   ()        const         { return root; }
    };

    sstat giveToSolver(PTRef root, FrameId push_id) {
        if (ts.cnfizeAndGiveToSolver(root, push_id) == l_False) return s_False;
        return s_Undef; }

    FContainer simplifyEqualities(vec<PtChild>& terms);

    PTRef rewriteMaxArity(PTRef);

    FContainer root_instance; // Contains the root of the instance once simplifications are done

    // helper private methods
    PushFrame& getLastFrame() const { return pfstore[frames.last()]; }
    bool isLastFrameUnsat() const { return getLastFrame().unsat; }
    void rememberLastFrameUnsat() { getLastFrame().unsat = true; }
    void rememberUnsatFrame(std::size_t frameIndex) {
        assert(frameIndex < frames.size());
        for (; frameIndex < frames.size(); ++frameIndex) {
            pfstore[frames.getFrameReference(frameIndex)].unsat = true;
        }
    }

    static std::unique_ptr<SimpSMTSolver> createInnerSolver(SMTConfig& config, THandler& thandler);

    static std::unique_ptr<Theory> createTheory(Logic & logic, SMTConfig & config);

  public:

    MainSolver(Logic& logic, SMTConfig& conf, std::string name)
        :
        theory(createTheory(logic, conf)),
        term_mapper(logic),
        thandler(getTheory(), term_mapper),
        smt_solver(createInnerSolver(conf, thandler)),
        logic(thandler.getLogic()),
        config(conf),
        pfstore(getTheory().pfstore),
        ts( config, logic, term_mapper, *smt_solver ),
        solver_name {std::move(name)},
        check_called(0),
        status(s_Undef),
        binary_init(false),
        root_instance(logic.getTerm_true())
    {
        conf.setUsedForInitiliazation();
        frames.push(pfstore.alloc());
        PushFrame& last = pfstore[frames.last()];
        last.push(logic.getTerm_true());
    }


    SMTConfig& getConfig() { return config; }
    SimpSMTSolver& getSMTSolver() { return *smt_solver; }

    THandler &getTHandler() { return thandler; }
    Logic    &getLogic()    { return logic; }
    Theory   &getTheory()   { return *theory; }
    sstat     push(PTRef root);
    void      push();
    bool      pop();
    sstat     insertFormula(PTRef root, char** msg);
    void      insertFormula(PTRef fla);

    void      initialize() { ts.solver.initialize(); ts.initialize(); }

    // Simplify frames (not yet simplified) until all are simplified or the instance is detected unsatisfiable.
    sstat simplifyFormulas(char** msg);
    sstat simplifyFormulas() { char* msg; sstat res = simplifyFormulas(&msg); if (res == s_Error) { printf("%s\n", msg); } return res; }
    sstat solve           ();
    sstat check           ();      // A wrapper for solve which simplifies the loaded formulas and initializes the solvers

    void printFramesAsQuery();

    sstat getStatus       ()       { return status; }
    bool  solverEmpty     () const { return ts.solverEmpty(); }
    bool  writeSolverState_smtlib2 (const char* file, char** msg);

    bool  writeFuns_smtlib2 (const char* file);

    void  addToConj(vec<vec<PtAsgn> >& in, vec<PTRef>& out); // Add the contents of in as disjuncts to out
    bool  writeSolverSplits_smtlib2(const char* file, char** msg);

    // Values
    lbool   getTermValue   (PTRef tr) const { return ts.getTermValue(tr); }

    // DEPRECATED. use the new Model structure
    ValPair getValue       (PTRef tr) const;
    void    getValues      (const vec<PTRef>&, vec<ValPair>&) const;

    // Returns model of the last formula (must be in satisiable state)
    std::unique_ptr<Model> getModel();

    void stop() { ts.solver.stop = true; }

    bool readFormulaFromFile(const char *file);
};

#endif //
