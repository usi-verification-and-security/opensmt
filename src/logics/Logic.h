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
#include "Tterm.h"
#ifdef PRODUCE_PROOF
#include "FlaPartitionMap.h"
#endif


class SStore;
struct SMTConfig;


class Logic {
    class TFun {
        SRef ret_sort;
        PTRef tr_body;
        char* name;
        vec<PTRef> args;
      public:
        TFun(const char* name_, const vec<PTRef>& args_, SRef ret_sort, PTRef tr_body)
            : ret_sort(ret_sort)
            , tr_body(tr_body)
        {
            name = (char*) malloc(strlen(name_)+1);
            strcpy(name, name_);
            args_.copyTo(args);
        }
        TFun() : ret_sort(SRef_Undef), tr_body(PTRef_Undef), name(NULL) {}
        TFun(TFun& other) : ret_sort(other.ret_sort), tr_body(other.tr_body), name(other.name) { other.args.copyTo(args); }
        TFun(const Tterm& t, SRef rsort) : ret_sort(rsort), tr_body(t.getBody())
        {
            name = (char*)malloc(strlen(t.getName())+1);
            strcpy(name, t.getName());
            t.getArgs().copyTo(args);
        }
        ~TFun() { free(name); }
        TFun& operator=(TFun& other) {
            if (&other != this) {
                free(name);
                ret_sort = other.ret_sort;
                tr_body = other.tr_body;
                name = other.name;
                other.name = NULL;
                other.args.copyTo(args);
            }
            return *this;
        }
        TFun& operator=(const TFun& other) {
            if (&other != this) {
                free(name);
                ret_sort = other.ret_sort;
                tr_body = other.tr_body;
                name = (char*)malloc(strlen(other.name)+1);
                strcpy(name, other.name);
                other.args.copyTo(args);
            }
            return *this;
        }
        const char* getName() const { return name; }
        SRef getRetSort() const { return ret_sort; }
        PTRef getBody() const { return tr_body; }
        const vec<PTRef>& getArgs() const { return args; }
    };
  protected:
    static const char* e_argnum_mismatch;
    static const char* e_bad_constant;

    // Information related to state serialization
    const static int buf_sz_idx             = 0;
    const static int equalities_offs_idx    = 1;
    const static int disequalities_offs_idx = 2;
    const static int ites_offs_idx          = 3;
    const static int ufsorts_offs_idx       = 4;
    const static int constants_offs_idx     = 5;

    Map<SymRef,bool,SymRefHash,Equal<SymRef> >      equalities;
    Map<SymRef,bool,SymRefHash,Equal<SymRef> >      disequalities;
    Map<SymRef,bool,SymRefHash,Equal<SymRef> >      ites;
    Map<SRef,bool,SRefHash,Equal<SRef> >            ufsorts;


#ifdef PRODUCE_PROOF
    //for partitions:
    //Map<PTRef,int,PTRefHash> partitions;
//    std::map<unsigned int, PTRef> partitions; // map of partition indices to PTRefs of partitions
    FlaPartitionMap flaPartitionMap;
    map<CRef, ipartitions_t> clause_class;
    map<Var, ipartitions_t> var_class;
#endif

    Map<const char*,TFun,StringHash,Equal<const char*> > defined_functions;
    vec<Tterm> defined_functions_vec; // A strange interface through the Tterms..

    vec<bool>           constants;
    vec<bool>           interpreted_functions;

    typedef struct{
        PTRef i;
        PTRef t;
        PTRef e;
        PTRef repr;
    } Ite;
    Map<PTRef,Ite,PTRefHash,Equal<PTRef>>    top_level_ites;

    SMTConfig&          config;
    IdentifierStore     id_store;
    SStore              sort_store;
    SymStore            sym_store;
  public:
    PtStore             term_store;
  protected:
    opensmt::Logic_t    logic_type;
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

    // For depth first search
    class pi {
      public:
        PTRef x;
        bool done;
        pi(PTRef x_) : x(x_), done(false) {}
    };

    virtual void visit(PTRef, Map<PTRef, PTRef, PTRefHash>&);
    virtual PTRef insertTermHash(SymRef, const vec<PTRef>&);

    void dumpFunction(ostream &, const TFun&);

    void conjoinItes(PTRef root, PTRef& new_root);

  private:
    vec<bool> appears_in_uf;
  public:
    vec<PTRef> propFormulasAppearingInUF;

  public:
    virtual bool okToPartition(PTRef) const { return true; } // Does the logic think this is a good var to partition on (while parallelizing)
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

    Logic(SMTConfig& c);
    virtual ~Logic();

    bool isIteVar(PTRef tr) const;// { return top_level_ites.has(tr); }
    PTRef getTopLevelIte(PTRef tr);// { return top_level_ites[tr].repr; }


    virtual void conjoinExtras(PTRef root, PTRef& new_root);// { conjoinItes(root, new_root); }

    virtual const opensmt::Logic_t getLogic() const;
    virtual const char * getName() const;

    // Identifiers
    IdRef       newIdentifier (const char* name)   ;//         { return id_store.newIdentifier(name); }
    IdRef       newIdentifier (const char* name, vec<int>& nl);//{ return id_store.newIdentifier(name, nl); }
    // Fetching sorts
    bool        containsSort  (const char* name)      const;// { return sort_store.containsSort(name); }
  protected:
    SRef        newSort       (IdRef idr, const char* name, vec<SRef>& tmp);// { return sort_store.newSort(idr, name, tmp); }
    PTRef       mkFun         (SymRef f, const vec<PTRef>& args, char** msg);
    PTRef       mkFun         (SymRef f, const vec<PTRef>& args) { char* msg; return mkFun(f, args, &msg); };
    void        markConstant  (PTRef ptr);
    void        markConstant  (SymId sid);

  public:
    SRef        getSortRef    (const char* name)      const;// { return sort_store[name]; }
    SRef        getSortRef    (const PTRef tr)        const;// { return getSortRef(getPterm(tr).symb()); }
    SRef        getSortRef    (const SymRef sr)       const;// { return getSym(sr).rsort(); }
    Sort*       getSort       (const SRef s)   ;//             { return sort_store[s]; }
    const char* getSortName   (const SRef s)  ;//              { return sort_store.getName(s); }

    // Symbols
    SymRef      newSymb       (const char* name, vec<SRef>& sort_args, char** msg)
                                                            { return sym_store.newSymb(name, sort_args); }
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
    virtual const char* getDefaultValue(const PTRef tr) const;
    PTRef       mkUninterpFun (SymRef f, const vec<PTRef>& args);
    // Boolean term generation
    PTRef       mkAnd         (vec<PTRef>&);
    PTRef       mkAnd         (PTRef a1, PTRef a2);// { vec<PTRef> tmp; tmp.push(a1); tmp.push(a2); return mkAnd(tmp); }
    PTRef       mkAnd         (const std::vector<PTRef> & v);// { vec<PTRef> tmp; for(PTRef ref : v) {tmp.push(ref);} return mkAnd(tmp); }
    PTRef       mkOr          (vec<PTRef>&);
    PTRef       mkOr          (PTRef a1, PTRef a2);// { vec<PTRef> tmp; tmp.push(a1); tmp.push(a2); return mkOr(tmp); }
    PTRef       mkOr          (const std::vector<PTRef> & v);// { vec<PTRef> tmp; for(PTRef ref : v) {tmp.push(ref);} return mkOr(tmp); }
    PTRef       mkXor         (vec<PTRef>&);
    PTRef       mkXor         (PTRef a1, PTRef a2);// { vec <PTRef> tmp; tmp.push(a1); tmp.push(a2); return mkXor(tmp); }
    PTRef       mkImpl        (vec<PTRef>&);
    PTRef       mkImpl        (PTRef _a, PTRef _b);
    PTRef       mkNot         (PTRef);
    PTRef       mkNot         (vec<PTRef>&);
    PTRef       mkIte         (vec<PTRef>&);
    PTRef       mkIte         (PTRef c, PTRef t, PTRef e);// { vec<PTRef> tmp; tmp.push(c); tmp.push(t); tmp.push(e); return mkIte(tmp); }


    // Generic equalities
    PTRef       mkEq          (vec<PTRef>& args);
    PTRef       mkEq          (PTRef a1, PTRef a2);// { vec<PTRef> v; v.push(a1); v.push(a2); return mkEq(v); }

    // Generic variables
    PTRef       mkVar         (SRef, const char*);
    // Generic constants
    virtual PTRef mkConst     (const char*, const char** msg);
    virtual PTRef mkConst     (SRef, const char*);

    SymRef      declareFun    (const char* fname, const SRef rsort, const vec<SRef>& args, char** msg, bool interpreted = false);
    bool        defineFun     (const char* fname, const vec<PTRef>& args, SRef ret_sort, const PTRef tr);
    vec<Tterm>& getFunctions  ();
    SRef        declareSort   (const char* id, char** msg);

    PTRef       mkBoolVar     (const char* name);

    void dumpHeaderToFile(ostream& dump_out);
    void dumpFormulaToFile(ostream& dump_out, PTRef formula, bool negate = false, bool toassert = true);
    void dumpChecksatToFile(ostream& dump_out);

    void dumpFunctions(ostream& dump_out);// { vec<const char*> names; defined_functions.getKeys(names); for (int i = 0; i < names.size(); i++) dumpFunction(dump_out, names[i]); }
    void dumpFunction(ostream& dump_out, const char* tpl_name);// { if (defined_functions.has(tpl_name)) dumpFunction(dump_out, defined_functions[tpl_name]); else printf("; Error: function %s is not defined\n", tpl_name); }
    void dumpFunction(ostream& dump_out, const std::string s);// { dumpFunction(dump_out, s.c_str()); }

    void dumpFunction(ostream& dump_out, const Tterm& t);// { dumpFunction(dump_out, TFun(t, getSortRef(t.getBody()))); }

    PTRef instantiateFunctionTemplate(const char* fname, Map<PTRef, PTRef, PTRefHash>&);

    bool implies(PTRef, PTRef); // Check the result with an external solver

#ifdef PRODUCE_PROOF
    PTRef getPartitionA(const ipartitions_t&);
    PTRef getPartitionB(const ipartitions_t&);
    bool verifyInterpolantA(PTRef, const ipartitions_t&);
    bool verifyInterpolantB(PTRef, const ipartitions_t&);
    bool verifyInterpolant(PTRef, const ipartitions_t&);

    ipartitions_t& getIPartitions(PTRef _t) { return term_store.getIPartitions(_t); }
    void setIPartitions(PTRef _t, const ipartitions_t& _p) { term_store.setIPartitions(_t, _p); }
    void addIPartitions(PTRef _t, const ipartitions_t& _p) { term_store.addIPartitions(_t, _p); }
    ipartitions_t& getIPartitions(SymRef _s) { return term_store.getIPartitions(_s); }
    void setIPartitions(SymRef _s, const ipartitions_t& _p) { term_store.setIPartitions(_s, _p); }
    void addIPartitions(SymRef _s, const ipartitions_t& _p) { term_store.addIPartitions(_s, _p); }
    void propagatePartitionMask(PTRef tr);

#endif

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
    bool        isDistinct(SymRef sr) const;// { return sr == getSym_distinct(); }
    bool        isDistinct(PTRef tr) const;// { return isDistinct(getPterm(tr).symb()); }
    bool        isIff(SymRef sr) const;// { return sr == getSym_eq(); }
    bool        isIff(PTRef tr) const;// { return isIff(getPterm(tr).symb()); }

    bool        isLit(PTRef tr) const;


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

    // Simplify an equality.  TODO: See if this could be combined with
    // simplifyTree
    bool simplifyEquality(PtChild& ptc, bool simplify);
    void simplifyDisequality(PtChild& ptc, bool simplify = true);
    // Simplify a term tree.  Return l_True, l_False, or l_Undef, if
    // simplification resulted in constant true or false, or neither,
    // respectively
    void        simplifyTree       (PTRef tr, PTRef& root_out);

    PTRef       resolveTerm        (const char* s, vec<PTRef>& args, char** msg);
    // XXX There's a need for non msg giving version
    virtual PTRef       insertTerm         (SymRef sym, vec<PTRef>& terms, char** msg);

    // Check if an assignment is already in some previous frame's unit
    // hashes (hashes) or the current hash (curr_hash)
    lbool isInHashes(vec<Map<PTRef,lbool,PTRefHash>*>& hashes, Map<PTRef,lbool,PTRefHash>& curr_hash, PtAsgn tr);
    // Top-level equalities based substitutions
    void getNewFacts(PTRef root, vec<Map<PTRef,lbool,PTRefHash>*>& prev_units, Map<PTRef,lbool,PTRefHash>& facts);
    bool varsubstitute(PTRef  root, const Map<PTRef, PtAsgn, PTRefHash> & substs, PTRef & tr_new);  // Do the substitution.  Return true if at least one substitution was done, and false otherwise.
    virtual lbool retrieveSubstitutions(const vec<PtAsgn>& units, Map<PTRef,PtAsgn,PTRefHash>& substs);




    bool contains(PTRef x, PTRef y);  // term x contains an occurrence of y

    PTRef learnEqTransitivity(PTRef); // Learn limited transitivity information


    bool       hasQuotableChars(const char* name) const;
    char*      protectName(const char* name) const;
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

#ifdef PRODUCE_PROOF
    //partitions:
    void assignPartition(unsigned int n, PTRef tr)
    {
        flaPartitionMap.store_top_level_fla_index(tr, n);
        term_store.assignPartition(n, tr);
    }

    ipartitions_t& getClauseClassMask(CRef l) { return clause_class[l]; }
    ipartitions_t& getVarClassMask(Var l) { return var_class[l]; }
    void addClauseClassMask(CRef l, const ipartitions_t& toadd);
    void addVarClassMask(Var l, const ipartitions_t& toadd);
    std::vector<PTRef> getPartitions()
    {
        return flaPartitionMap.get_top_level_flas();
    }

    std::vector<PTRef> getPartitions(ipartitions_t const & mask){
        throw std::logic_error{"Not supported at the moment!"};
    }

    unsigned getNofPartitions() { return flaPartitionMap.getNoOfPartitions(); }

    void transferPartitionMembership(PTRef old, PTRef new_ptref)
    {
        this->addIPartitions(new_ptref, getIPartitions(old));
        flaPartitionMap.transferPartitionMembership(old, new_ptref);
    }

    int getPartitionIndex(PTRef ref) const {
        return flaPartitionMap.getPartitionIndex(ref);
    }

#endif // PRODUCE_PROOF
    // Statistics
    int subst_num; // Number of substitutions

    void collectStats(PTRef, int& n_of_conn, int& n_of_eq, int& n_of_uf, int& n_of_if);

    inline int     verbose                       ( ) const;// { return config.verbosity(); }
};

#endif // LOGIC_H

