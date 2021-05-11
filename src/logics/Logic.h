/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2015 Antti Hyvarinen

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
#include "SymStore.h"
#include "PtStore.h"
#include "SStore.h"
#include "CgTypes.h"
#include "LogicFactory.h"
#include "OsmtApiException.h"
#include "FunctionTools.h"
#include <cassert>
#include <cstring>
#include <cstdlib>


class SStore;

class Logic {
protected:
    static std::size_t abstractValueCount;
    static const char* e_argnum_mismatch;
    static const char* e_bad_constant;

    Map<SymRef,bool,SymRefHash,Equal<SymRef> >      equalities;
    Map<SymRef,bool,SymRefHash,Equal<SymRef> >      disequalities;
    Map<SymRef,bool,SymRefHash,Equal<SymRef> >      ites;
    Map<SRef,SymRef,SRefHash>                       sortToIte;
    Map<SRef,bool,SRefHash,Equal<SRef> >            ufsorts;
    Map<SRef,PTRef,SRefHash,Equal<SRef>>            defaultValueForSort;

    bool isKnownToUser(SymRef sr) const { return getSymName(sr)[0] != s_abstract_value_prefix[0]; }
    int distinctClassCount;

    class DefinedFunctions {
        std::map<std::string,TemplateFunction> defined_functions;
        std::vector<std::string> defined_functions_names;

    public:
        bool has(const char* name) const { return defined_functions.find(name) != defined_functions.end(); }
        bool has(const std::string& name) const { return defined_functions.find(name) != defined_functions.end(); }

        void insert(const std::string& name, TemplateFunction && templ) {
            assert(not has(name));
            defined_functions_names.emplace_back(name);
            defined_functions[defined_functions_names.back()] = std::move(templ);
        }

        TemplateFunction & operator[](const char* name) {
            assert(has(name));
            return defined_functions[name];
        }

        void getKeys(vec<const char*> & keys_out) {
            for (auto k : defined_functions_names) {
                keys_out.push(strdup(k.c_str()));
            }
        }
    };
    DefinedFunctions defined_functions;

    vec<bool>           constants;
    vec<bool>           interpreted_functions;




    IdentifierStore     id_store;
    SStore              sort_store;
    SymStore            sym_store;
    PtStore             term_store;
    SymRef              sym_TRUE;
    SymRef              sym_FALSE;
    SymRef              sym_ANON;
    SymRef              sym_AND;
    SymRef              sym_OR;
    SymRef              sym_XOR;
    SymRef              sym_NOT;
    SymRef              sym_UF_NOT;
    SymRef              sym_EQ;
    SymRef              sym_IMPLIES;
    SymRef              sym_DISTINCT;
    SymRef              sym_ITE;

    SRef                sort_BOOL;
    PTRef               term_TRUE;
    PTRef               term_FALSE;


    virtual PTRef insertTermHash(SymRef, const vec<PTRef>&);

    void dumpFunction(ostream &, const TemplateFunction&);

  private:
    enum class UFAppearanceStatus {
        unseen, removed, appears
    };
    vec<UFAppearanceStatus> appears_in_uf;
    void unsetAppearsInUF(PTRef tr);

  public:
    vec<PTRef> propFormulasAppearingInUF;
    std::size_t getNumberOfTerms() const { return term_store.getNumberOfTerms(); }
    bool existsTermHash(SymRef, const vec<PTRef>&);
    static const char*  tk_val_uf_default;
    static const char*  tk_val_bool_default;
    static const char*  tk_true;
    static const char*  tk_false;
    static const char*  tk_anon;   // The anonymous symbol for enodes for propositional formulas
    static const char*  tk_uf_not; // The symbol for propositional not in UF.
    static const char*  tk_not;
    static const char*  tk_equals;
    static const char*  tk_implies;
    static const char*  tk_and;
    static const char*  tk_or;
    static const char*  tk_xor;
    static const char*  tk_distinct;
    static const char*  tk_ite;


    static const char*  s_sort_bool;
    static const char*  s_ite_prefix;
    static const char*  s_framev_prefix;
    static const char*  s_abstract_value_prefix;

    Logic();
    virtual ~Logic();

    virtual PTRef conjoinExtras(PTRef root);

    virtual const char * getName() const { return "QF_UF"; }
    virtual const opensmt::Logic_t getLogic() const { return opensmt::Logic_t::QF_UF; }

    // Identifiers
    IdRef       newIdentifier (const char* name)   ;//         { return id_store.newIdentifier(name); }
    IdRef       newIdentifier (const char* name, vec<int>& nl);//{ return id_store.newIdentifier(name, nl); }
    // Fetching sorts
    bool        containsSort  (const char* name)      const;// { return sort_store.containsSort(name); }
  protected:
    SymRef      newSymb       (const char* name, vec<SRef> const & sort_args) { return sym_store.newSymb(name, sort_args); }
    SRef        newSort       (IdRef idr, const char* name, vec<SRef>& tmp);// { return sort_store.newSort(idr, name, tmp); }
    PTRef       mkFun         (SymRef f, const vec<PTRef>& args);
    void        markConstant  (PTRef ptr);
    void        markConstant  (SymId sid);

  public:
    SRef        getSortRef    (const char* name)      const;// { return sort_store[name]; }
    SRef        getSortRef    (const PTRef tr)        const;// { return getSortRef(getPterm(tr).symb()); }
    SRef        getSortRef    (const SymRef sr)       const;// { return getSym(sr).rsort(); }
    Sort*       getSort       (const SRef s)   ;//             { return sort_store[s]; }
    const char* getSortName   (const SRef s)          const;// { return sort_store.getName(s); }

    // Symbols
    Symbol& getSym              (const SymRef s)        { return sym_store[s]; }
    const Symbol& getSym        (const SymRef s)        const { return sym_store[s]; }
    const Symbol& getSym        (const PTRef tr)        const { return getSym(getPterm(tr).symb()); }
    SymRef      getSymRef       (const PTRef tr)        const { return getPterm(tr).symb(); }
    const char* getSymName      (const PTRef tr)        const { return sym_store.getName(getPterm(tr).symb()); }
    const char* getSymName      (const SymRef s)        const { return sym_store.getName(s); }
    vec<SymRef>& symNameToRef (const char* s)               { return sym_store.nameToRef(s); }
    bool        hasSym        (const char* s)         const { return sym_store.contains(s); }
    bool        commutes      (const SymRef s)        const { return getSym(s).commutes(); }
    // Terms

    Pterm&      getPterm      (const PTRef tr)              { return term_store[tr];  }
    const Pterm& getPterm     (const PTRef tr)        const { return term_store[tr];  }
    PtermIter   getPtermIter  ()                            { return term_store.getPtermIter(); }

    // Default values for the logic

    // Deprecated! Use getDefaultValuePTRef instead
    virtual const char* getDefaultValue(const PTRef tr) const;

    // Returns the default value of the sort of the argument term
    PTRef getDefaultValuePTRef(const PTRef tr) const { return getDefaultValuePTRef(getSortRef(tr)); }

    // Returns the default value of the given sort
    virtual PTRef getDefaultValuePTRef(const SRef sref) const;

    PTRef       mkUninterpFun (SymRef f, const vec<PTRef>& args);
    // Boolean term generation
    PTRef       mkAnd         (const vec<PTRef>&);
    PTRef       mkAnd         (PTRef a1, PTRef a2) { return mkAnd({a1, a2}); }
    PTRef       mkOr          (const vec<PTRef>&);
    PTRef       mkOr          (PTRef a1, PTRef a2) { return mkOr({a1, a2}); }
    PTRef       mkXor         (const vec<PTRef>&);
    PTRef       mkXor         (PTRef a1, PTRef a2) { return mkXor({a1, a2}); }
    PTRef       mkImpl        (const vec<PTRef>&);
    PTRef       mkImpl        (PTRef _a, PTRef _b);
    PTRef       mkNot         (PTRef);
    PTRef       mkNot         (vec<PTRef>&);
    PTRef       mkIte         (const vec<PTRef>&);
    PTRef       mkIte         (PTRef c, PTRef t, PTRef e) { return mkIte({c, t, e}); }


    // Generic equalities
    PTRef       mkEq          (const vec<PTRef>& args);
    PTRef       mkEq          (PTRef a1, PTRef a2) { return mkEq({a1, a2}); }

    // General disequalities
    PTRef       mkDistinct    (vec<PTRef>& args);
    PTRef       mkDistinct    (vec<PTRef>&& args) { return mkDistinct(args); }

    // Generic variables
    PTRef       mkVar         (SRef, const char*);
    PTRef       mkUniqueAbstractValue(SRef);

    // Generic constants
    virtual PTRef mkConst     (const char*, const char** msg);
    virtual PTRef mkConst     (SRef, const char*);

    SymRef      declareFun    (const char* fname, const SRef rsort, const vec<SRef>& args, char** msg, bool interpreted = false);
    bool        defineFun     (const char* fname, const vec<PTRef>& args, SRef ret_sort, const PTRef tr);
    SRef        declareSort   (const char* id, char** msg);

    PTRef       mkBoolVar     (const char* name);

    void dumpHeaderToFile(ostream& dump_out) const;
    void dumpFormulaToFile(ostream& dump_out, PTRef formula, bool negate = false, bool toassert = true) const;
    void dumpChecksatToFile(ostream& dump_out) const;

    void dumpFunctions(ostream& dump_out);// { vec<const char*> names; defined_functions.getKeys(names); for (int i = 0; i < names.size(); i++) dumpFunction(dump_out, names[i]); }
    void dumpFunction(ostream& dump_out, const char* tpl_name);// { if (defined_functions.has(tpl_name)) dumpFunction(dump_out, defined_functions[tpl_name]); else printf("; Error: function %s is not defined\n", tpl_name); }
    void dumpFunction(ostream& dump_out, const std::string s);// { dumpFunction(dump_out, s.c_str()); }

    PTRef instantiateFunctionTemplate(const char* fname, Map<PTRef, PTRef, PTRefHash>&);



    // The Boolean connectives
    SymRef        getSym_true      ()              const;// { return sym_TRUE;     }
    SymRef        getSym_false     ()              const;// { return sym_FALSE;    }
    SymRef        getSym_anon      ()              const    { return sym_ANON; }
    SymRef        getSym_and       ()              const;// { return sym_AND;      }
    SymRef        getSym_or        ()              const;// { return sym_OR;       }
    SymRef        getSym_xor       ()              const;// { return sym_XOR;      }
    SymRef        getSym_not       ()              const;// { return sym_NOT;      }
    SymRef        getSym_eq        ()              const;// { return sym_EQ;       }
    SymRef        getSym_ite       ()              const;// { return sym_ITE;      }
    SymRef        getSym_implies   ()              const;// { return sym_IMPLIES;  }
    SymRef        getSym_distinct  ()              const;// { return sym_DISTINCT; }
    SymRef        getSym_uf_not    ()              const    { return sym_UF_NOT;   }
    SRef          getSort_bool     ()              const;// { return sort_BOOL;    }


    PTRef         getTerm_true     ()              const;// { return term_TRUE;  }
    PTRef         getTerm_false    ()              const;// { return term_FALSE; }

    bool          isEquality       (SymRef tr)     const;// { return equalities.has(tr);    }
    bool          isEquality       (PTRef tr)      const;// { return equalities.has(term_store[tr].symb());}
    virtual bool  isUFEquality     (PTRef tr)      const;// { return isEquality(tr) && !hasSortBool(getPterm(tr)[0]); }
    virtual bool  isTheoryEquality (PTRef tr)      const;// { return isUFEquality(tr); }
    bool          isDisequality    (SymRef tr)     const;// { return disequalities.has(tr); }
    bool          isDisequality    (PTRef tr)      const;// { return disequalities.has(term_store[tr].symb()); }
    bool          isIte            (SymRef tr)     const;// { return ites.has(tr);          }
    bool          isIte            (PTRef tr)      const;// { return ites.has(term_store[tr].symb()); }
    bool          isNonBoolIte     (SymRef sr)     const { return isIte(sr) and getSortRef(sr) != sort_BOOL; }
    bool          isNonBoolIte     (PTRef tr)      const { return isNonBoolIte(getPterm(tr).symb()); }

    // tr is a theory symbol if it is not a boolean variable, nor one of the standard
    // boolean operators (and, not, or, etc...)
    // Note that equivalence over non-boolean terms is not a Boolean operator.
    bool         isTheorySymbol     (SymRef tr)       const;
    // True for terms (PTRef) that are of interest to theory solver and should be declared to the solver. Only such terms should be declared to the theory solver
    bool         isTheoryTerm       (PTRef tr)        const;
    bool         isBooleanOperator  (SymRef tr)       const;
    bool         isBooleanOperator  (PTRef tr)        const;// { return isBooleanOperator(term_store[tr].symb()); }
    virtual bool isBuiltinSort      (const SRef sr)   const;// { return sr == sort_BOOL; }
    virtual bool isBuiltinConstant  (const SymRef sr) const;// { return isConstant(sr) && (sr == sym_TRUE || sr == sym_FALSE); }
    bool         isBuiltinConstant  (const PTRef tr)  const;// { return isBuiltinConstant(getPterm(tr).symb()); }
    virtual bool isBuiltinFunction  (const SymRef sr) const;
    bool         isConstant         (const SymRef sr) const;
    bool         isConstant         (PTRef tr)        const;// { return isConstant(getPterm(tr).symb()); }
    bool         isUFTerm           (PTRef tr)        const;// { return isUFSort(getSortRef(tr)); }
    bool         isUFSort           (const SRef sr)   const;// { return ufsorts.has(sr); }

    bool         appearsInUF        (PTRef tr)        const;
    void         setAppearsInUF     (PTRef tr);
    virtual vec<PTRef> getNestedBoolRoots (PTRef tr)  const;

    bool        isVar              (SymRef sr)     const ;//{ return sym_store[sr].nargs() == 0 && !isConstant(sr); }
    bool        isVar              (PTRef tr)      const;// { return isVar(getPterm(tr).symb()); }
    bool        isVarOrIte         (SymRef sr)     const { return isVar(sr) or isIte(sr); }
    bool        isVarOrIte         (PTRef tr)      const { return isVarOrIte(getPterm(tr).symb()); }
    virtual bool isAtom            (PTRef tr)      const;
    bool        isBoolAtom         (PTRef tr)      const;// { return hasSortBool(tr) && isVar(tr); }
    // Check if term is an uninterpreted predicate.
    virtual bool isUP              (PTRef)         const;
    virtual bool isUF              (PTRef)         const;
    virtual bool isUF              (SymRef)        const;
    virtual bool isIF              (PTRef)         const;
    virtual bool isIF              (SymRef)        const;

    bool        isAnd(PTRef tr)  const ;//{ return getPterm(tr).symb() == getSym_and(); }
    bool        isAnd(SymRef sr) const;// { return sr == getSym_and(); }
    bool        isOr (PTRef tr)  const ;//{ return getPterm(tr).symb() == getSym_or (); }
    bool        isOr (SymRef sr) const;// { return sr == getSym_or(); }
    bool        isNot(PTRef tr)  const;// { return getPterm(tr).symb() == getSym_not(); }
    bool        isNot(SymRef sr) const ;//{ return sr == getSym_not(); }
    bool        isXor(SymRef sr) const;// { return sr == getSym_xor(); }
    bool        isXor(PTRef tr)  const;// { return isXor(getPterm(tr).symb()); }
    bool        isImplies(SymRef sr) const;// { return sr == getSym_implies(); }
    bool        isImplies(PTRef tr)  const;// { return isImplies(getPterm(tr).symb()); }
    bool        isTrue(SymRef sr) const;// { return sr == getSym_true(); }
    bool        isTrue(PTRef tr)  const ;//{ return isTrue(getPterm(tr).symb()); }
    bool        isFalse(SymRef sr) const;// { return sr == getSym_false(); }
    bool        isFalse(PTRef tr)  const;// { return isFalse(getPterm(tr).symb()); }
    bool        isAnon(SymRef sr) const { return sr == getSym_anon(); }
    bool        isIff(SymRef sr) const;// { return sr == getSym_eq(); }
    bool        isIff(PTRef tr) const;// { return isIff(getPterm(tr).symb()); }


    bool        hasSortBool(PTRef tr) const;// { return sym_store[getPterm(tr).symb()].rsort() == sort_BOOL; }
    bool        hasSortBool(SymRef sr) const;// { return sym_store[sr].rsort() == sort_BOOL; }
    //bool        hasSortInt (PTRef tr) const { return sym_store[getPterm(tr).symb()].rsort() == sort_INTEGER; }


    // Return the corresponding equivalence term if yes,
    // PTRef_Undef otherwise.
    PTRef       lookupUPEq         (PTRef tr);

    // Returns an equality over args if term store contains one, otherwise returns PTRef_Undef.
    // args is sorted before lookup, but not simplified otherwise
    PTRef       hasEquality        (vec<PTRef>& args);
    // Override for different logics...
    virtual bool declare_sort_hook  (SRef sr);
    inline bool isPredef           (string&)        const ;//{ return false; };

    // Simplify a term tree.  Return l_True, l_False, or l_Undef, if
    // simplification resulted in constant true or false, or neither,
    // respectively
    void        simplifyTree       (PTRef tr, PTRef& root_out);

    PTRef       resolveTerm        (const char* s, vec<PTRef>& args, char** msg);

    virtual PTRef       insertTerm         (SymRef sym, vec<PTRef>& terms);
    virtual PTRef       insertTerm         (SymRef sym, vec<PTRef>&& terms) { return insertTerm(sym, terms); }

    // Top-level equalities based substitutions
    void getNewFacts(PTRef root, Map<PTRef, lbool, PTRefHash> & facts);
    virtual lbool retrieveSubstitutions(const vec<PtAsgn>& units, Map<PTRef,PtAsgn,PTRefHash>& substs);
    template <typename TAsgn>
    void substitutionsTransitiveClosure(Map<PTRef, TAsgn, PTRefHash> & substs);

public:


    bool contains(PTRef x, PTRef y);  // term x contains an occurrence of y

    PTRef learnEqTransitivity(PTRef); // Learn limited transitivity information


    bool       hasQuotableChars(const char* name) const;
    char*      protectName(const char* name) const;
    char*      protectName(const std::string& name) const;
    virtual char* printTerm_       (PTRef tr, bool l, bool s) const;
    virtual char* printTerm        (PTRef tr)                 const;// { return printTerm_(tr, false, false); }
    virtual char* printTerm        (PTRef tr, bool l, bool s) const ;//{ return printTerm_(tr, l, s); }
    virtual char* pp(PTRef tr) const; // A pretty printer
    char*       printSym           (SymRef sr) const;
    virtual void termSort(vec<PTRef>& v) const;// { sort(v, LessThan_PTRef()); }

    void  purify           (PTRef r, PTRef& p, lbool& sgn) const;//{p = r; sgn = l_True; while (isNot(p)) { sgn = sgn^1; p = getPterm(p)[0]; }}

#ifdef PEDANTIC_DEBUG
    void compareSymStore(SymStore& other) { sym_store.compare(other); }
    void compareIdStore(IdentifierStore& other) {}
    void compareSortStore(SStore& other) { }
    void compareTermStore(PtStore& other) { }// term_store.compare(other); }
#endif

    // Statistics
    int subst_num; // Number of substitutions

    void collectStats(PTRef, int& n_of_conn, int& n_of_eq, int& n_of_uf, int& n_of_if);

    inline int     verbose                       ( ) const;// { return config.verbosity(); }
};



#endif // LOGIC_H