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
    static const char* e_bad_constant;

    // Information related to state serialization
    const static int buf_sz_idx             = 0;
    const static int equalities_offs_idx    = 1;
    const static int disequalities_offs_idx = 2;
    const static int ites_offs_idx          = 3;

    Map<SymRef,bool,SymRefHash,Equal<SymRef> >      equalities;
    Map<SymRef,bool,SymRefHash,Equal<SymRef> >      disequalities;
    Map<SymRef,bool,SymRefHash,Equal<SymRef> >      ites;

    IdentifierStore&    id_store;
    SStore&             sort_store;
    SymStore&           sym_store;
  public:
    SMTConfig&          config;
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

    SymRef              sym_Real_NEG;
    SymRef              sym_Real_MINUS;
    SymRef              sym_Real_PLUS;
    SymRef              sym_Real_TIMES;
    SymRef              sym_Real_DIV;
    SymRef              sym_Real_LEQ;
    SymRef              sym_Real_LT;
    SymRef              sym_Real_GEQ;
    SymRef              sym_Real_GT;

    SRef                sort_BOOL;
    SRef                sort_REAL;

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

    static const char*  tk_real_neg;
    static const char*  tk_real_minus;
    static const char*  tk_real_plus;
    static const char*  tk_real_times;
    static const char*  tk_real_div;
    static const char*  tk_real_leq;
    static const char*  tk_real_lt;
    static const char*  tk_real_geq;
    static const char*  tk_real_gt;

    static const char*  s_sort_bool;
    static const char*  s_sort_real;

    Logic(SMTConfig& c, IdentifierStore& i, SStore& s, SymStore& t, PtStore& pt);

    bool          setLogic    (const char* l);
    bool          isSet       ()                      const { return is_set;    }
    const string& getName     ()                      const { return name;      }

    // Fetching sorts
    SRef        getSortRef    (const char* name)      const { return sort_store[name]; }
    SRef        getSort       (const PTRef tr)        const { return getSym(getPterm(tr).symb()).rsort(); }
    Sort*       getSort       (const SRef s)                { return sort_store[s]; }
    const char* getSortName   (const SRef s)                { return sort_store.getName(s); }

    // Symbols
    SymRef      newSymb       (const char* name, vec<SRef>& sort_args, char** msg)
                                                            { return sym_store.newSymb(name, sort_args, msg); }
//    bool        hasSym        (const SymRef s)        const { return sym_store.contains(s); }
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
    PTRef       mkConst       (const char*, char** msg);
    PTRef       mkConst       (SRef, const char*);

    SymRef      declareFun    (const char* fname, const SRef rsort, const vec<SRef>& args, char** msg);
    SRef        declareSort   (const char* id, char** msg);
    SRef        declareSort_Real(char** msg);
    PTRef       mkFun         (SymRef f, vec<PTRef>& args, char** msg);
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
    SRef          getSort_real     ()              const { return sort_REAL;    }

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

    // XXX The two Boolean constants are vars.  This is confusing.
    bool        isVar              (PTRef tr)      const { return term_store[tr].nargs() == 0; }
    bool        isConst            (PTRef tr)      const { return isTrue(tr) || isFalse(tr); }
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
    bool        declare_sort_hook  (SRef sr);
    inline bool isPredef           (string&)        const { return false; };

    // Implement logic-aware simplifications
    void        simplify           (SymRef& s, vec<PTRef>& args);
    // Wrapper for simplifying terms
    void        simplify           (PTRef& tr);
    // Simplify an equality.  TODO: See if this could be combined with
    // simplifyTree
    bool simplifyEquality(PtChild& ptc, bool simplify);
    void simplifyDisequality(PtChild& ptc, bool simplify = true);
    // Simplify a term tree.  Return l_True, l_False, or l_Undef, if
    // simplification resulted in constant true or fale, or neither,
    // respectively
    lbool       simplifyTree       (PTRef tr);
    PTRef       resolveTerm        (const char* s, vec<PTRef>& args, char** msg);
    // XXX There's a need for non msg giving version
    PTRef       insertTerm         (SymRef sym, vec<PTRef>& terms, char** msg);

    void        serializeLogicData(int*& logicdata_buf) const;
    void        deserializeLogicData(const int* logicdata_buf);

    void        serializeTermSystem(int*& termstore_buf, int*& symstore_buf, int*& idstore_buf, int*& sortstore_buf, int*& logicdata_buf) const;
    void        deserializeTermSystem(const int* termstore_buf, const int* symstore_buf, const int* idstore_buf, const int* sortstore_buf, const int* logicdata_buf);
// Debugging
    char*       printTerm          (PTRef tr)       const { return term_store.printTerm(tr); }

#ifdef PEDANTIC_DEBUG
    void compareSymStore(SymStore& other) { sym_store.compare(other); }
    void compareIdStore(IdentifierStore& other) {}
    void compareSortStore(SStore& other) { }
    void compareTermStore(PtStore& other) { }// term_store.compare(other); }
#endif

};

#endif // LOGIC_H

