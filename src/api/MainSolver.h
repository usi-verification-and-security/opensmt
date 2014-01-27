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
                     Logic::s_sort_bool, logic.getSort(logic.getSort(root))->getCanonName());
            return s_Error; }
        formulas.push(root);
        return s_Undef; }

    sstat simplifyFormulas(char** err_msg);
    lbool solve() { return ts.solve(); }
//    static void getTermList(PTRef tr, vec<PtChild>&, Logic& l);
};
