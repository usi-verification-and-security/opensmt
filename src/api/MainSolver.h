#include "Logic.h"
#include "SimpSMTSolver.h"
#include "Egraph.h"
#include "Tseitin.h"

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
    Logic&         logic;
    TermMapper&    tmap;
    Egraph&        uf_solver;
    SimpSMTSolver& sat_solver;
    Tseitin&       ts;

  public:
    MainSolver(Logic& l, TermMapper& tm, Egraph& uf_s, SimpSMTSolver& sat_s, Tseitin& t) :
          logic(l)
        , tmap(tm)
        , uf_solver(uf_s)
        , sat_solver(sat_s)
        , ts(t)
        {}
    sstat insertTermRoot(PTRef, char**);
    void getTermList(PTRef tr, vec<PtChild>&);
};
