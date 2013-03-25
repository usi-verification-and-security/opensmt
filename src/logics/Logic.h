#ifndef LOGIC_H
#define LOGIC_H
//#include "smtsolvers/SMTConfig.h"
//#include "SimpSMTSolver.h"
//#include "Tseitin.h"
#include "Sort.h"
// For TRefHash
#include "SymStore.h"
#include "PtStore.h"

class SStore;
class TStore;

class Logic {
  private:
    Map<SymRef,bool,SymRefHash,Equal<SymRef> >      equalities;
    Map<SymRef,bool,SymRefHash,Equal<SymRef> >      disequalities;
    Map<SymRef,bool,SymRefHash,Equal<SymRef> >      ites;
    Map<PTRef,PTRef,PTRefHash,Equal<PTRef> >        UP_map; // maps uninterpreted predicates to their equality terms

    SMTConfig&          config;
    SStore&             sort_store;
    SymStore&           sym_store;
  public:
    PtStore&            term_store;
  private:
    bool                is_set;
    string              name;
    SymRef              sym_TRUE;
    SymRef              sym_FALSE;
    SymRef              sym_AND;
    SymRef              sym_OR;
    SymRef              sym_XOR;
    SymRef              sym_NOT;
    SymRef              sym_EQ;
    SymRef              sym_IMPLIES;
    SymRef              sym_DISTINCT;
    SymRef              sym_ITE;
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
    Logic(SMTConfig& c, SStore& s, SymStore& t, PtStore& pt);


    bool          setLogic         (const char* l);
    bool          isSet            ()              const { return is_set;    }
    const string& getName          ()              const { return name;      }

    // The Boolean connectives
    SymRef        getSym_true      ()              const { return sym_TRUE;     }
    SymRef        getSym_false     ()              const { return sym_FALSE;    }
    SymRef        getSym_and       ()              const { return sym_AND;      }
    SymRef        getSym_or        ()              const { return sym_OR;       }
    SymRef        getSym_xor       ()              const { return sym_XOR;      }
    SymRef        getSym_not       ()              const { return sym_NOT;      }
    SymRef        getSym_eq        ()              const { return sym_EQ;       }
    SymRef        getSym_ite       ()              const { return sym_ITE;      }
    SymRef        getSym_implies   ()              const { return sym_IMPLIES;  }
    SymRef        getSym_distinct  ()              const { return sym_DISTINCT; }
    SRef          getSort_bool     ()              const { return sort_BOOL;    }

    PTRef         getTerm_true     ()              const { return term_TRUE;  }
    PTRef         getTerm_false    ()              const { return term_FALSE; }

    bool          isEquality       (SymRef tr)     const { return equalities.contains(tr);    }
    bool          isDisequality    (SymRef tr)     const { return disequalities.contains(tr); }
    bool          isIte            (SymRef tr)     const { return ites.contains(tr);          }
    // tr is a theory symbol if it is not a boolean variable, nor one of the standard
    // boolean operators (and, not, or, etc...)
    bool        isTheorySymbol(SymRef tr)    const;
    bool        isTheoryTerm(PTRef tr)       const;
    bool        isBooleanOperator(SymRef tr) const;

    // Check if term is an uninterpreted predicate.
    bool        isUP(PTRef) const;

    // Return the corresponding equivalence term if yes,
    // PTRef_Undef otherwise.
    PTRef       lookupUPEq       (PTRef tr) const;

    // Override for different logics...
    bool        declare_sort_hook(Sort* s);
    inline bool isPredef(string&) const { return false; };

};

#endif // LOGIC_H

