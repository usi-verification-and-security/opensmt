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
#include "MapWithKeys.h"
#include "OsmtApiException.h"
#include "FunctionTools.h"
#include "TypeUtils.h"
#include <cassert>
#include <cstring>
#include <cstdlib>


class SStore;

class Logic {
  public:
    using SubstMap = MapWithKeys<PTRef,PTRef,PTRefHash>;
  protected:
    static std::size_t abstractValueCount;
    static const char* e_argnum_mismatch;
    static const char* e_bad_constant;

    Map<SymRef,bool,SymRefHash,Equal<SymRef> >      equalities;
    Map<SymRef,bool,SymRefHash,Equal<SymRef> >      disequalities;
    Map<SymRef,bool,SymRefHash,Equal<SymRef> >      ites;
    Map<SRef,SymRef,SRefHash>                       sortToEquality;
    Map<SRef,SymRef,SRefHash>                       sortToDisequality;
    Map<SRef,SymRef,SRefHash>                       sortToIte;
    Map<SRef,bool,SRefHash,Equal<SRef> >            ufsorts;
    Map<SRef,PTRef,SRefHash,Equal<SRef>>            defaultValueForSort;

    opensmt::Logic_t const logicType;

    bool isKnownToUser(std::string_view name) const { return name[0] != s_abstract_value_prefix[0]; }
    bool isKnownToUser(SymRef sr) const { return isKnownToUser(getSymName(sr)); }
    int distinctClassCount;

    class DefinedFunctions {
        std::unordered_map<std::string,TemplateFunction> defined_functions;
        std::vector<std::string> defined_functions_names;

    public:
        bool has(const std::string& name) const { return defined_functions.find(name) != defined_functions.end(); }

        void insert(const std::string& name, TemplateFunction && templ) {
            assert(not has(name));
            defined_functions_names.emplace_back(name);
            defined_functions[name] = std::move(templ);
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


    SStore              sort_store;
    SymStore            sym_store;
    PtStore             term_store;

    SSymRef             sym_IndexedSort;

    SRef                sort_BOOL;
    PTRef               term_TRUE;
    PTRef               term_FALSE;

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

    void dumpFunction(std::ostream &, const TemplateFunction&);

  private:
    enum class UFAppearanceStatus {
        unseen, removed, appears
    };
    vec<UFAppearanceStatus> appears_in_uf;
    void unsetAppearsInUF(PTRef tr);

  public:
    vec<PTRef> propFormulasAppearingInUF;
    std::size_t getNumberOfTerms() const { return term_store.getNumberOfTerms(); }
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
    static const char*  tk_indexed;


    static const char*  s_sort_bool;
    static const char*  s_ite_prefix;
    static const char*  s_framev_prefix;
    static const char*  s_abstract_value_prefix;

    Logic(opensmt::Logic_t type);
    virtual ~Logic();

    virtual PTRef conjoinExtras(PTRef root);

    virtual std::string const getName() const { return opensmt::QFLogicToProperties.at(logicType).name; }
    opensmt::Logic_t getLogic() const { return logicType; }

    bool hasUFs() const { return opensmt::QFLogicToProperties.at(logicType).ufProperty.hasUF; }
    bool hasIntegers() const { return opensmt::QFLogicToProperties.at(logicType).arithProperty.hasInts; }
    bool hasReals() const { return opensmt::QFLogicToProperties.at(logicType).arithProperty.hasReals; }

  protected:
    PTRef       mkFun         (SymRef f, vec<PTRef>&& args);
    void        markConstant  (PTRef ptr);
    void        markConstant  (SymId sid);

  public:
    SRef                getSortRef (PTRef tr)  const;
    SRef                getSortRef (SymRef sr) const;
    std::string         printSort  (SRef s)    const;
    std::size_t         getSortSize(SRef s)    const;
    SRef declareUninterpretedSort(std::string const &);

    SRef        getUniqueArgSort(SymRef sr)           const;
    SRef        getUniqueArgSort(PTRef tr)            const { return getUniqueArgSort(getSymRef(tr)); }

    // Symbols
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

    PTRef       mkUninterpFun (SymRef f, vec<PTRef>&& args);
    PTRef       mkUninterpFun (SymRef f, vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkUninterpFun(f, std::move(tmp)); }

    // Boolean term generation
    PTRef       mkAnd         (vec<PTRef>&&);
    PTRef       mkAnd         (vec<PTRef> const& args) { vec<PTRef> tmp; args.copyTo(tmp); return mkAnd(std::move(tmp)); }
    PTRef       mkAnd         (PTRef a1, PTRef a2) { return mkAnd({a1, a2}); }

    PTRef       mkOr          (vec<PTRef>&&);
    PTRef       mkOr          (vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkOr(std::move(tmp)); }
    PTRef       mkOr          (PTRef a1, PTRef a2) { return mkOr({a1, a2}); }

    PTRef       mkXor         (vec<PTRef>&&);
    PTRef       mkXor         (PTRef a1, PTRef a2) { return mkXor({a1, a2}); }
    PTRef       mkImpl        (vec<PTRef>&&);
    PTRef       mkImpl        (PTRef a1, PTRef a2) { return mkImpl({a1, a2}); }
    PTRef       mkNot         (PTRef);
    PTRef       mkNot         (vec<PTRef>&&);
    PTRef       mkIte         (vec<PTRef>&&);
    PTRef       mkIte         (PTRef c, PTRef t, PTRef e) { return mkIte({c, t, e}); }


    // Generic equalities
    PTRef       mkEq          (vec<PTRef>&& args);
    PTRef       mkEq          (vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkEq(std::move(tmp)); }
    PTRef       mkEq          (PTRef a1, PTRef a2) { return mkBinaryEq(a1, a2); }
protected:
    virtual PTRef mkBinaryEq(PTRef lhs, PTRef rhs);
    bool isInternalSort(SRef) const;
    void newUninterpretedSortHandler(SRef);

public:

    // General disequalities
    PTRef       mkDistinct    (vec<PTRef>&& args);

    // Generic variables
    PTRef       mkVar         (SRef, const char*, bool isInterpreted = false);
    PTRef       mkUniqueAbstractValue(SRef);

    // Generic constants
    virtual PTRef mkConst     (const char*);
    virtual PTRef mkConst     (SRef, const char*);


    SymRef      declareFun(std::string const & fname, SRef rsort, vec<SRef> const & args, SymbolConfig const & symbolConfig);
    SymRef      declareFun(std::string const & fname, SRef rsort, vec<SRef> const & args) { return declareFun(fname, rsort, args, SymConf::Default); }
    SymRef      declareFun_NoScoping(std::string const & s, SRef rsort, vec<SRef> const & args) { return declareFun(s, rsort, args, SymConf::NoScoping); }
    SymRef      declareFun_NoScoping_LeftAssoc(std::string const & s, SRef rsort, vec<SRef> const & args) { return declareFun(s, rsort, args, SymConf::NoScopingLeftAssoc); }
    SymRef      declareFun_NoScoping_RightAssoc(std::string const & s, SRef rsort, vec<SRef> const & args) { return declareFun(s, rsort, args, SymConf::NoScopingRightAssoc); }
    SymRef      declareFun_NoScoping_Chainable(std::string const & s, SRef rsort, vec<SRef> const & args) { return declareFun(s, rsort, args, SymConf::NoScopingChainable); }
    SymRef      declareFun_NoScoping_Pairwise(std::string const & s, SRef rsort, vec<SRef> const & args) { return declareFun(s, rsort, args, SymConf::NoScopingPairwise); }
    SymRef      declareFun_Commutative_NoScoping_LeftAssoc(std::string const & s, SRef rsort, vec<SRef> const & args) { return declareFun(s, rsort, args, SymConf::CommutativeNoScopingLeftAssoc); }
    SymRef      declareFun_Commutative_NoScoping_Chainable(std::string const & s, SRef rsort, vec<SRef> const & args) { return declareFun(s, rsort, args, SymConf::CommutativeNoScopingChainable); }
    SymRef      declareFun_Commutative_NoScoping_Pairwise(std::string const & s, SRef rsort, vec<SRef> const & args) { return declareFun(s, rsort, args, SymConf::CommutativeNoScopingPairwise); }

    SymRef      declareFun_LeftAssoc(std::string const & s, SRef rsort, vec<SRef> const & args) { return declareFun(s, rsort, args, SymConf::LeftAssoc); }
    SymRef      declareFun_RightAssoc(std::string const & s, SRef rsort, vec<SRef> const & args) { return declareFun(s, rsort, args, SymConf::RightAssoc); }
    SymRef      declareFun_Chainable(std::string const & s, SRef rsort, vec<SRef> const & args) { return declareFun(s, rsort, args, SymConf::Chainable); }
    SymRef      declareFun_Pairwise(std::string const & s, SRef rsort, vec<SRef> const & args) { return declareFun(s, rsort, args, SymConf::Pairwise); }

    bool        defineFun     (const char* fname, const vec<PTRef>& args, SRef ret_sort, const PTRef tr);
    void        instantiateFunctions(SRef);

    bool        hasSortSymbol(SortSymbol const &);
    bool        peekSortSymbol(SortSymbol const &, SSymRef&);
    SSymRef     declareSortSymbol(SortSymbol symbol);
    SRef        getSort(SSymRef, vec<SRef> && args);

    PTRef       mkBoolVar     (const char* name);

    void dumpHeaderToFile(std::ostream& dump_out) const;
    void dumpFormulaToFile(std::ostream& dump_out, PTRef formula, bool negate = false, bool toassert = true) const;
    void dumpChecksatToFile(std::ostream& dump_out) const;

    void dumpFunctions(std::ostream& dump_out);// { vec<const char*> names; defined_functions.getKeys(names); for (int i = 0; i < names.size(); i++) dumpFunction(dump_out, names[i]); }
    void dumpFunction(std::ostream& dump_out, const char* tpl_name);// { if (defined_functions.has(tpl_name)) dumpFunction(dump_out, defined_functions[tpl_name]); else printf("; Error: function %s is not defined\n", tpl_name); }
    void dumpFunction(std::ostream& dump_out, const std::string s);// { dumpFunction(dump_out, s.c_str()); }

    PTRef instantiateFunctionTemplate(TemplateFunction const & tmplt, vec<PTRef> const & args);
    PTRef instantiateFunctionTemplate(const char * name, vec<PTRef> const & args);

    SSymRef       getSortSymIndexed()              const { return sym_IndexedSort; }

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
    virtual bool isBuiltinSortSym   (const SSymRef ssr) const;
    virtual bool isBuiltinConstant  (const SymRef sr) const;// { return isConstant(sr) && (sr == sym_TRUE || sr == sym_FALSE); }
    bool         isBuiltinConstant  (const PTRef tr)  const;// { return isBuiltinConstant(getPterm(tr).symb()); }
    virtual bool isBuiltinFunction  (const SymRef sr) const;
    bool         isConstant         (const SymRef sr) const;
    bool         isConstant         (PTRef tr)        const;
    bool         yieldsSortUninterpreted (PTRef tr)   const;
    bool         isUFSort           (const SRef sr)   const;

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
    bool        isInterpreted      (SymRef sr)     const { return sym_store.isInterpreted(sr); }
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


    // Returns an equality over args if term store contains one, otherwise returns PTRef_Undef.
    // args is sorted before lookup, but not simplified otherwise
    PTRef       hasEquality        (vec<PTRef>& args);

    PTRef       resolveTerm(const char* s, vec<PTRef>&& args, SRef sortRef = SRef_Undef, SymbolMatcher symbolMatcher = SymbolMatcher::Any);
    virtual PTRef insertTerm (SymRef sym, vec<PTRef> && args);
    PTRef insertTerm(SymRef sym, vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return insertTerm(sym, std::move(tmp)); }

    // Top-level equalities based substitutions
    bool getNewFacts(PTRef root, MapWithKeys<PTRef, lbool, PTRefHash> & facts);
    virtual opensmt::pair<lbool,SubstMap> retrieveSubstitutions(const vec<PtAsgn>& units);

    void substitutionsTransitiveClosure(SubstMap & substs);

    bool contains(PTRef x, PTRef y);  // term x contains an occurrence of y

    PTRef learnEqTransitivity(PTRef); // Learn limited transitivity information


    bool hasQuotableChars(std::string const & name) const;
    bool isReservedWord(std::string const & name) const;
    bool isAmbiguousUninterpretedNullarySymbolName(std::string_view name) const { return term_store.isAmbiguousNullarySymbolName(name); };
    std::string protectName(std::string const & name, bool isInterpreted) const;
    std::string disambiguateName(std::string const & protectedName, SRef retSort, bool isNullary, bool isInterpreted) const;
    std::string protectName(SymRef sr) const { return protectName(getSymName(sr), getSym(sr).isInterpreted()); };
    virtual std::string printTerm_ (PTRef tr, bool l, bool s) const;
    std::string printTerm          (PTRef tr)                 const { return printTerm_(tr, false, false); }
    std::string printTerm          (PTRef tr, bool l, bool s) const { return printTerm_(tr, l, s); }
    std::string pp(PTRef tr) const; // A pretty printer

    std::string   printSym          (SymRef sr) const;
    virtual void termSort(vec<PTRef>& v) const;// { sort(v, LessThan_PTRef()); }

    void  purify           (PTRef r, PTRef& p, lbool& sgn) const;//{p = r; sgn = l_True; while (isNot(p)) { sgn = sgn^1; p = getPterm(p)[0]; }}

#ifdef PEDANTIC_DEBUG
    void compareSymStore(SymStore& other) { sym_store.compare(other); }
    void compareIdStore(IdentifierStore& other) {}
    void compareSortStore(SStore& other) { }
    void compareTermStore(PtStore& other) { }// term_store.compare(other); }
#endif

    // Statistics

    void collectStats(PTRef, int& n_of_conn, int& n_of_eq, int& n_of_uf, int& n_of_if);

    bool typeCheck(SymRef sym, vec<PTRef> const & args, std::string & why) const;
    inline int     verbose                       ( ) const;// { return config.verbosity(); }
};

#endif // LOGIC_H

