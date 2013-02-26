#ifndef LOGIC_H
#define LOGIC_H
//#include "smtsolvers/SMTConfig.h"
//#include "SimpSMTSolver.h"
//#include "Tseitin.h"
#include "Sort.h"
// For TRefHash
#include "TStore.h"
#include "PtStore.h"

class SStore;
class TStore;

class Logic {
  private:
    Map<TRef,bool,TRefHash,Equal<TRef> >        equalities;
    Map<TRef,bool,TRefHash,Equal<TRef> >        disequalities;
    Map<TRef,bool,TRefHash,Equal<TRef> >        ites;
    Map<PTRef,PTRef,PTRefHash,Equal<PTRef> >    UP_map; // maps uninterpreted predicates to their equality terms

    SMTConfig&          config;
    SStore&             sort_store;
    TStore&             sym_store;
    PtStore&            term_store;
    bool                is_set;
    string              name;
    TRef                sym_TRUE;
    TRef                sym_FALSE;
    TRef                sym_AND;
    TRef                sym_OR;
    TRef                sym_XOR;
    TRef                sym_NOT;
    TRef                sym_EQ;
    TRef                sym_IMPLIES;
    TRef                sym_ITE;
    SRef                sort_BOOL;

    PTRef               term_TRUE;
    PTRef               term_FALSE;

    static const char*  tk_true;
    static const char*  tk_false;
    static const char*  tk_not;
    static const char*  tk_equals;
    static const char*  tk_implies;
    static const char*  tk_and;
    static const char*  tk_or;
    static const char*  tk_xor;
    static const char*  tk_distinct;
    static const char*  tk_ite;

  public:
    Logic(SMTConfig& c, SStore& s, TStore& t, PtStore& pt);


    bool          setLogic         (const char* l);
    bool          isSet            ()              const { return is_set;    }
    const string& getName          ()              const { return name;      }

    // The Boolean connectives
    TRef          getSym_true      ()              const { return sym_TRUE;   }
    TRef          getSym_false     ()              const { return sym_FALSE;  }
    TRef          getSym_and       ()              const { return sym_AND;    }
    TRef          getSym_or        ()              const { return sym_OR;     }
    TRef          getSym_xor       ()              const { return sym_XOR;    }
    TRef          getSym_not       ()              const { return sym_NOT;    }
    TRef          getSym_eq        ()              const { return sym_EQ;     }
    TRef          getSym_ite       ()              const { return sym_ITE;    }
    TRef          getSym_implies   ()              const { return sym_IMPLIES;}
    SRef          getSort_bool     ()              const { return sort_BOOL;  }

    PTRef          getTerm_true    ()              const { return term_TRUE;  }
    PTRef          getTerm_false   ()              const { return term_FALSE; };

    bool        isEquality    (TRef tr) const { return equalities.contains(tr);    }
    bool        isDisequality (TRef tr) const { return disequalities.contains(tr); }
    bool        isIte         (TRef tr) const { return ites.contains(tr);          }
    // tr is a theory symbol if it is not a boolean variable, nor one of the standard
    // boolean operators (and, not, or, etc...)
    bool        isTheorySymbol(TRef tr)    const;
    bool        isTheoryTerm(PTRef tr)     const { return isTheorySymbol(term_store[tr].symb()); }
    bool        isBooleanOperator(TRef tr) const;
    // Check if term is an uninterpreted predicate.
    // Return the corresponding equivalence term if yes,
    // PTRef_Undef otherwise.
    PTRef       lookupUPEq       (PTRef tr) const;

    // Override for different logics...
    bool        declare_sort_hook(Sort* s);
    inline bool isPredef(string&) const { return false; };

};

#endif // LOGIC_H

