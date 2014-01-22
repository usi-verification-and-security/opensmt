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


  public:
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

    static const char*  s_sort_bool;

    Logic(SMTConfig& c, SStore& s, SymStore& t, PtStore& pt);

    bool          setLogic    (const char* l);
    bool          isSet       ()                      const { return is_set;    }
    const string& getName     ()                      const { return name;      }

    // Fetching sorts
    SRef        getSortRef    (const char* name)      const { return sort_store[name]; }
    SRef        getSort       (const PTRef tr)        const { return getSym(getPterm(tr).symb()).rsort(); }
    Sort*       getSort       (const SRef s)                { return sort_store[s]; }

    // Symbols
    SymRef      newSymb       (const char* name, vec<SRef>& sort_args)
                                                            { return sym_store.newSymb(name, sort_args); }
    Symbol&     getSym        (const SymRef s)        const { return sym_store[s]; }
    vec<SymRef>& symNameToRef (const char* s)               { return sym_store.nameToRef(s); }
    // Terms

    Pterm&      getPterm      (const PTRef tr)        const { return term_store[tr];  }

    // Boolean term generation
    PTRef       mkAnd         (vec<PTRef>& args);
    PTRef       mkOr          (vec<PTRef>& args);
    PTRef       mkImpl        (vec<PTRef>& args);
    PTRef       mkNot         (PTRef);


    // Generic equalities
    PTRef       mkEq          (vec<PTRef>& args);

    // Generic constants
    PTRef       mkConst            (SRef, const char*);

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
    bool          isEquality       (PTRef tr)      const { return equalities.contains(term_store[tr].symb());}
    bool          isDisequality    (SymRef tr)     const { return disequalities.contains(tr); }
    bool          isDisequality    (PTRef tr)      const { return disequalities.contains(term_store[tr].symb()); }
    bool          isIte            (SymRef tr)     const { return ites.contains(tr);          }

    // tr is a theory symbol if it is not a boolean variable, nor one of the standard
    // boolean operators (and, not, or, etc...)
    bool        isTheorySymbol     (SymRef tr)     const;
    bool        isTheoryTerm       (PTRef tr)      const;
    bool        isBooleanOperator  (SymRef tr)     const;

    bool        isVar              (PTRef tr)      const { return term_store[tr].nargs() == 0; }

    // Check if term is an uninterpreted predicate.
    bool        isUP               (PTRef)         const;

    // Boolean term identification
    bool        isAnd              (PTRef ptr)            { return term_store[ptr].symb() == sym_AND; }
    bool        isOr               (PTRef ptr)            { return term_store[ptr].symb() == sym_OR; }

    // Return the corresponding equivalence term if yes,
    // PTRef_Undef otherwise.
    PTRef       lookupUPEq         (PTRef tr);

    // Override for different logics...
    bool        declare_sort_hook  (Sort* s);
    inline bool isPredef           (string&)        const { return false; };

    PTRef       resolveTerm        (const char* s, vec<PTRef>& args);
    PTRef       insertTerm         (SymRef sym, vec<PTRef>& terms);

// Debugging
    char*       printTerm          (PTRef tr)       const { return term_store.printTerm(tr); }
};

#endif // LOGIC_H

