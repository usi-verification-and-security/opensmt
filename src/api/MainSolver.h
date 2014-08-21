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


#include "Logic.h"
#include "SimpSMTSolver.h"
#include "Egraph.h"
#include "Tseitin.h"
#include "simplifiers/TopLevelPropagate.h"

class sstat {
    char value;
    explicit sstat(int v) : value(v) {}
  public:
    sstat() : value(0) {}
    bool operator == (sstat s) const { return value == s.value; }
    bool operator != (sstat s) const { return value != s.value; }
    friend sstat toSstat(int v);

};

inline sstat toSstat(int v) {return sstat(v); }

const sstat s_True  = toSstat( 1);
const sstat s_False = toSstat(-1);
const sstat s_Undef = toSstat( 0);
const sstat s_Error = toSstat( 2);

class MainSolver {
  private:
    const static int map_offs_idx        = 0;
    const static int termstore_offs_idx  = 1;
    const static int symstore_offs_idx   = 2;
    const static int idstore_offs_idx    = 3;
    const static int sortstore_offs_idx  = 4;
    const static int logicstore_offs_idx = 5;
    const static int cnf_offs_idx        = 6;

    class pi {
      public:
        PTRef x;
        bool done;
        pi(PTRef x_) : x(x_), done(false) {}
    };
    Logic&         logic;
    TermMapper&    tmap;
    Egraph&        uf_solver;
    SimpSMTSolver& sat_solver;
    Tseitin&       ts;
    vec<PTRef>     formulas;

    TopLevelPropagator tlp;

    class FContainer {
        PTRef   root;

      public:
              FContainer(PTRef r) : root(r)     {}
        void  setRoot   (PTRef r)               { root = r; }
        PTRef getRoot   ()        const         { return root; }
    };

    void expandItes(FContainer& fc, vec<PtChild>& terms) const;

    sstat giveToSolver(PTRef root) {
        if (ts.cnfizeAndGiveToSolver(root) == l_False) return s_False;
        return s_Undef; }

    FContainer simplifyEqualities(vec<PtChild>& terms);
    FContainer propFlatten(FContainer fc);
#ifdef ENABLE_SHARING_BUG
    FContainer mergeEnodeArgs(PTRef fr, Map<PTRef, PTRef, PTRefHash>& cache, Map<PTRef, int, PTRefHash>& occs);
    FContainer rewriteMaxArity(FContainer fc, Map<PTRef, int, PTRefHash>& occs);

#endif

  public:
    MainSolver(Logic& l, TermMapper& tm, Egraph& uf_s, SimpSMTSolver& sat_s, Tseitin& t) :
          logic(l)
        , tmap(tm)
        , uf_solver(uf_s)
        , sat_solver(sat_s)
        , ts(t)
        , tlp(logic,ts)
        { formulas.push(logic.getTerm_true()); }

    sstat insertFormula(PTRef root, char** msg) {
        if (logic.getSort(root) != logic.getSort_bool()) {
            asprintf(msg, "Top-level assertion sort must be %s, got %s",
                     Logic::s_sort_bool, logic.getSortName(logic.getSort(root)));
            return s_Error; }
        formulas.push(root);
        return s_Undef; }

    sstat simplifyFormulas(char** err_msg);
    lbool solve() { return ts.solve(); }
//    static void getTermList(PTRef tr, vec<PtChild>&, Logic& l);
    bool readSolverState(const char* file, char** msg);
    bool writeSolverState(const char* file, char** msg);
};
