#ifndef LOGIC_H
#define LOGIC_H
//#include "smtsolvers/SMTConfig.h"
//#include "SimpSMTSolver.h"
//#include "Tseitin.h"
#include "Sort.h"
// For TRefHash
#include "TStore.h"

class SStore;
class TStore;

class Logic {
  private:
    Map<TRef,bool,TRefHash,Equal<TRef> >        equalities;
    Map<TRef,bool,TRefHash,Equal<TRef> >        disequalities;

    SMTConfig&          config;
    SStore&             sort_store;
    TStore&             term_store;
    bool                is_set;
    string              name;
    TRef                sym_TRUE;
    TRef                sym_FALSE;
    TRef                sym_AND;
    TRef                sym_OR;
    TRef                sym_XOR;
    TRef                sym_NOT;
    TRef                sym_EQ;
    SRef                sort_BOOL;
//    Egraph              egraph;
//    SimpSMTSolver       solver;
//    Tseitin             cnfizer;

  public:
    Logic(SMTConfig& c, SStore& s, TStore& t);

    bool          setLogic         (const char* l);
    bool          isSet            ()              const { return is_set;    }
    const string& getName          ()              const { return name;      }

    // The Boolean connectives
    TRef          getSym_true      ()              const { return sym_TRUE;  }
    TRef          getSym_false     ()              const { return sym_FALSE; }
    TRef          getSym_and       ()              const { return sym_AND;   }
    TRef          getSym_or        ()              const { return sym_OR;    }
    TRef          getSym_xor       ()              const { return sym_XOR;   }
    TRef          getSym_not       ()              const { return sym_NOT;   }
    TRef          getSym_eq        ()              const { return sym_EQ;    }
    SRef          getSort_bool     ()              const { return sort_BOOL; }

    bool        isEquality    (TRef tr) const { return equalities.contains(tr); }
    bool        isDisequality (TRef tr) const { return disequalities.contains(tr); }
    // Override for different logics...
    bool        declare_sort_hook(Sort* s);
    inline bool isPredef(string&) const { return false; };
};

#endif // LOGIC_H

