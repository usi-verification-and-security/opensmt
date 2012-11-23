#ifndef LOGIC_H
#define LOGIC_H
#include "smtsolvers/SMTConfig.h"
//#include "SimpSMTSolver.h"
//#include "Tseitin.h"
#include "Sort.h"

class SStore;
class TStore;

class Logic {
  private:
    SMTConfig&          config;
    SStore&             sort_store;
    TStore&             term_store;
    bool                is_set;
    string              name;
//    Egraph              egraph;
//    SimpSMTSolver       solver;
//    Tseitin             cnfizer;

  public:
    Logic(SMTConfig& c, SStore& s, TStore& t);

    bool          setLogic         (const char* l)                         ;
    bool          isSet            ()              const { return is_set; };
    const string& getName          ()              const { return name; }  ;

    // Override for different logics...
    bool        declare_sort_hook(Sort* s);
    inline bool isPredef(string&) const { return false; };
};

#endif // LOGIC_H

