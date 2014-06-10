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
    static const char* e_argnum_mismatch;

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

    // For depth first search
    class pi {
      public:
        PTRef x;
        bool done;
        pi(PTRef x_) : x(x_), done(false) {}
    };

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
    SymRef      newSymb       (const char* name, vec<SRef>& sort_args, const char** msg)
                                                            { return sym_store.newSymb(name, sort_args, msg); }
    bool        hasSym        (const SymRef s)        const { return sym_store.contains(s); }
    Symbol&     getSym        (const SymRef s)        const { return sym_store[s]; }
    const char* getSymName    (const PTRef tr)        const { return sym_store.getName(getPterm(tr).symb()); }
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
    PTRef       mkConst       (SRef, const char*);

    SymRef      declareFun    (const char* fname, const SRef rsort, const vec<SRef>& args, const char** msg);
    SRef        declareSort   (const char* id, const char** msg);
    PTRef       mkFun         (SymRef f, vec<PTRef>& args, const char** msg);
    PTRef       mkBoolVar     (const char* name) { return mkConst(getSort_bool(), name); }


    // Clone a term
    PTRef       cloneTerm     (const PTRef&);

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
    bool          isIte            (PTRef tr)      const { return ites.contains(term_store[tr].symb()); }

    // tr is a theory symbol if it is not a boolean variable, nor one of the standard
    // boolean operators (and, not, or, etc...)
    // Note that equivalence over non-boolean terms is not a Boolean operator.
    bool        isTheorySymbol     (SymRef tr)     const;
    bool        isTheoryTerm       (PTRef tr)      const;
    bool        isBooleanOperator  (SymRef tr)     const;
    bool        isBooleanOperator  (PTRef tr)      const { return isBooleanOperator(term_store[tr].symb()); }

    bool        isVar              (PTRef tr)      const { return term_store[tr].nargs() == 0; }
    bool        isAtom             (PTRef tr)      const;
    // Check if term is an uninterpreted predicate.
    bool        isUP               (PTRef)         const;

    bool        isAnd(PTRef tr)  const { return getPterm(tr).symb() == getSym_and(); }
    bool        isAnd(SymRef sr) const { return sr == getSym_and(); }
    bool        isOr (PTRef tr)  const { return getPterm(tr).symb() == getSym_or (); }
    bool        isOr (SymRef sr) const { return sr == getSym_or(); }
    bool        isNot(PTRef tr)  const { return getPterm(tr).symb() == getSym_not(); }
    bool        isNot(SymRef sr) const { return sr == getSym_not(); }
    bool        isXor(SymRef sr) const { return sr == getSym_xor(); }
    bool        isXor(PTRef tr)  const { return isXor(getPterm(tr).symb()); }
    bool        isImplies(SymRef sr) const { return sr == getSym_implies(); }
    bool        isImplies(PTRef tr)  const { return isImplies(getPterm(tr).symb()); }
    bool        isTrue(SymRef sr) const { return sr == getSym_true(); }
    bool        isTrue(PTRef tr)  const { return isTrue(getPterm(tr).symb()); }
    bool        isFalse(SymRef sr) const { return sr == getSym_false(); }
    bool        isFalse(PTRef tr)  const { return isTrue(getPterm(tr).symb()); }
    bool        isDistinct(SymRef sr) const { return sr == getSym_distinct(); }
    bool        isDistinct(PTRef tr) const { return isDistinct(getPterm(tr).symb()); }
    bool        isIff(SymRef sr) const { return sr == getSym_eq(); }
    bool        isIff(PTRef tr) const { return isIff(getPterm(tr).symb()); }

    bool        isLit(PTRef tr) const;


    // Return the corresponding equivalence term if yes,
    // PTRef_Undef otherwise.
    PTRef       lookupUPEq         (PTRef tr);

    // Returns an equality over args if term store contains one, otherwise returns PTRef_Undef.
    // args is sorted before lookup, but not simplified otherwise
    PTRef       hasEquality        (vec<PTRef>& args);
    // Override for different logics...
    bool        declare_sort_hook  (Sort* s);
    inline bool isPredef           (string&)        const { return false; };

    // Implement logic-aware simplifications
    void        simplify           (SymRef& s, vec<PTRef>& args);
    // Wrapper for simplifying terms
    void        simplify           (PTRef& tr);
    // Simplify a term tree.  Return l_True, l_False, or l_Undef, if
    // simplification resulted in constant true or fale, or neither,
    // respectively
    lbool       simplifyTree       (PTRef tr);
    PTRef       resolveTerm        (const char* s, vec<PTRef>& args, char** msg);
    PTRef       insertTerm         (SymRef sym, vec<PTRef>& terms, const char** msg);

// Debugging
    char*       printTerm          (PTRef tr)       const { return term_store.printTerm(tr); }
};

#endif // LOGIC_H

