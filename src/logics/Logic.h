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
#include "SSort.h"
#include "SymStore.h"
#include "PtStore.h"
//#include "Tterm.h"

class SStore;
class TStore;

// For breaking substitution loops
struct NStatus { uint32_t x; bool operator== (const NStatus& o) const { return o.x == x; } };
static NStatus ns_inStack  = {0};
static NStatus ns_complete = {1};
static NStatus ns_unseen   = {2};
static NStatus ns_undef    = {INT32_MAX};

class Logic {
  protected:
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



    //for partitions:
    vec<PTRef> assertions;
    vec<PTRef> assertions_simp;
//    vec<Tterm*> functions;
#ifdef PRODUCE_PROOF
    map<CRef, ipartitions_t> clause_class;
    map<Var, ipartitions_t> var_class;
    map<PTRef, PTRef> flat2orig;
#endif

    Map<const char*,PTRef,StringHash,Equal<const char*> > defined_functions;

    vec<SymRef>         sortToEquality;
    vec<bool>           constants;
    vec<bool>           interpreted_functions;
    Map<PTRef,PTRef,PTRefHash,Equal<PTRef> >    top_level_ites;

    SMTConfig&          config;
    IdentifierStore     id_store;
    SStore              sort_store;
    SymStore            sym_store;
  public:
    PtStore             term_store;
  protected:
    Logic_t             logic_type;
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

    virtual void visit(PTRef, Map<PTRef, PTRef, PTRefHash>&);
    PTRef insertTermHash(SymRef, const vec<PTRef>&);

  public:
    bool existsTermHash(SymRef, const vec<PTRef>&);
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
    static const char*  s_ite_prefix;
    static const char*  s_framev_prefix;

    Logic(SMTConfig& c);
    ~Logic();

    bool isIteVar(PTRef tr) { return top_level_ites.has(tr); }
    PTRef getTopLevelIte(PTRef tr) { return top_level_ites[tr]; }
    void addTopLevelIte(PTRef i, PTRef var)
    {
        if (i == PTRef_Undef || var == PTRef_Undef)
            assert(false);

        assert(!top_level_ites.has(var));
        top_level_ites.insert(var, i);
    }

    void conjoinItes(PTRef root, PTRef& new_root)
    {
        vec<PTRef> queue;
        Map<PTRef,bool,PTRefHash> seen;
        queue.push(root);
        vec<PTRef> args;
        while (queue.size() != 0) {
            PTRef el = queue.last();
            queue.pop();
            if (seen.has(el)) continue;
            if (isVar(el) && isIteVar(el)) {
                args.push(getTopLevelIte(el));
                queue.push(getTopLevelIte(el));
            }
            for (int i = 0; i < getPterm(el).size(); i++)
                queue.push(getPterm(el)[i]);
            seen.insert(el, true);
        }

        args.push(root);
        new_root = mkAnd(args);
    }

    virtual const Logic_t getLogic() const;
    virtual const char* getName()    const;

    // Identifiers
    IdRef       newIdentifier (const char* name)            { return id_store.newIdentifier(name); }
    IdRef       newIdentifier (const char* name, vec<int>& nl){ return id_store.newIdentifier(name, nl); }
    // Fetching sorts
    bool        containsSort  (const char* name)      const { return sort_store.containsSort(name); }
    SRef        newSort       (IdRef idr, const char* name, vec<SRef>& tmp) { return sort_store.newSort(idr, name, tmp); }
    SRef        getSortRef    (const char* name)      const { return sort_store[name]; }
    SRef        getSortRef    (const PTRef tr)              { return getSym(getPterm(tr).symb()).rsort(); }
    Sort*       getSort       (const SRef s)                { return sort_store[s]; }
    const char* getSortName   (const SRef s)                { return sort_store.getName(s); }

    // Symbols
    SymRef      newSymb       (const char* name, vec<SRef>& sort_args, char** msg)
                                                            { return sym_store.newSymb(name, sort_args, msg); }
//    bool        hasSym        (const SymRef s)        const { return sym_store.contains(s); }
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

    // Boolean term generation
    PTRef       mkAnd         (vec<PTRef>&);
    PTRef       mkAnd         (PTRef a1, PTRef a2) { vec<PTRef> tmp; tmp.push(a1); tmp.push(a2); return mkAnd(tmp); }
    PTRef       mkOr          (vec<PTRef>&);
    PTRef       mkOr          (PTRef a1, PTRef a2) { vec<PTRef> tmp; tmp.push(a1); tmp.push(a2); return mkOr(tmp); }
    PTRef       mkXor         (vec<PTRef>&);
    PTRef       mkXor         (PTRef a1, PTRef a2) { vec <PTRef> tmp; tmp.push(a1); tmp.push(a2); return mkXor(tmp); }
    PTRef       mkImpl        (vec<PTRef>&);
    PTRef       mkImpl        (PTRef _a, PTRef _b);
    PTRef       mkNot         (PTRef);
    PTRef       mkNot         (vec<PTRef>&);
    PTRef       mkIte         (vec<PTRef>&);
    PTRef       mkIte         (PTRef c, PTRef t, PTRef e) { vec<PTRef> tmp; tmp.push(c); tmp.push(t); tmp.push(e); return mkIte(tmp); }


    // Generic equalities
    PTRef       mkEq          (vec<PTRef>& args);
    PTRef       mkEq          (PTRef a1, PTRef a2) { vec<PTRef> v; v.push(a1); v.push(a2); return mkEq(v); }

    // Generic variables
    PTRef       mkVar         (SRef, const char*);
    // Generic constants
    virtual PTRef mkConst     (const char*, const char** msg);
    virtual PTRef mkConst     (SRef, const char*);

    SymRef      declareFun    (const char* fname, const SRef rsort, const vec<SRef>& args, char** msg, bool interpreted = false);
    bool        defineFun     (const char* fname, const PTRef tr);
    SRef        declareSort   (const char* id, char** msg);
    PTRef       mkFun         (SymRef f, const vec<PTRef>& args, char** msg);
    PTRef       mkBoolVar     (const char* name);

    void dumpHeaderToFile(ostream& dump_out);
    void dumpFormulaToFile(ostream& dump_out, PTRef formula, bool negate = false);
    void dumpChecksatToFile(ostream& dump_out);

//    PTRef instantiateFunctionTemplate(Tterm&, map<PTRef, PTRef>);
//    vec<Tterm*>& getFunctions() { return functions; }
//    void addFunction(Tterm* f) { functions.push(f); }

#ifdef PRODUCE_PROOF

    PTRef getPartitionA(const ipartitions_t&);
    PTRef getPartitionB(const ipartitions_t&);
    bool implies(PTRef, PTRef);
    bool verifyInterpolantA(PTRef, const ipartitions_t&);
    bool verifyInterpolantB(PTRef, const ipartitions_t&);
    bool verifyInterpolant(PTRef, const ipartitions_t&);


    // Partitions
    void setOriginalAssertion(PTRef flat, PTRef orig)
    {
        flat2orig[flat] = orig;
    }
    bool hasOriginalAssertion(PTRef flat)
    {
        return flat2orig.find(flat) != flat2orig.end();
    }
    PTRef getOriginalAssertion(PTRef flat)
    {
        assert(flat2orig.find(flat) != flat2orig.end());
        return flat2orig[flat];
    }
    ipartitions_t getIPartitions(PTRef _t) { return term_store.getIPartitions(_t); }
    void setIPartitions(PTRef _t, ipartitions_t _p) { term_store.setIPartitions(_t, _p); }
    void addIPartitions(PTRef _t, ipartitions_t _p) { term_store.addIPartitions(_t, _p); }
    ipartitions_t getIPartitions(SymRef _s) { return term_store.getIPartitions(_s); }
    void setIPartitions(SymRef _s, ipartitions_t _p) { term_store.setIPartitions(_s, _p); }
    void addIPartitions(SymRef _s, ipartitions_t _p) { term_store.addIPartitions(_s, _p); }
#endif

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

    bool          isEquality       (SymRef tr)     const { return equalities.has(tr);    }
    bool          isEquality       (PTRef tr)      const { return equalities.has(term_store[tr].symb());}
    virtual bool  isUFEquality     (PTRef tr)      const { return isEquality(tr) && !hasSortBool(getPterm(tr)[0]); }
    virtual bool  isTheoryEquality (PTRef tr)      const { return isUFEquality(tr); }
    bool          isDisequality    (SymRef tr)     const { return disequalities.has(tr); }
    bool          isDisequality    (PTRef tr)      const { return disequalities.has(term_store[tr].symb()); }
    bool          isIte            (SymRef tr)     const { return ites.has(tr);          }
    bool          isIte            (PTRef tr)      const { return ites.has(term_store[tr].symb()); }

    // tr is a theory symbol if it is not a boolean variable, nor one of the standard
    // boolean operators (and, not, or, etc...)
    // Note that equivalence over non-boolean terms is not a Boolean operator.
    bool        isTheorySymbol     (SymRef tr)     const;
    bool        isTheoryTerm       (PTRef tr)      const;
    bool        isBooleanOperator  (SymRef tr)     const;
    bool        isBooleanOperator  (PTRef tr)      const { return isBooleanOperator(term_store[tr].symb()); }
    virtual bool isBuiltinSort     (const SRef sr) const { return sr == sort_BOOL; }
    bool        isConstant         (const SymRef sr) const;
    bool        isConstant         (PTRef tr)      const { return isConstant(getPterm(tr).symb()); }

    bool        isVar              (SymRef sr)     const { return sym_store[sr].nargs() == 0 && !isConstant(sr); }
    bool        isVar              (PTRef tr)      const { return isVar(getPterm(tr).symb()); }
    bool        isAtom             (PTRef tr)      const;
    bool        isBoolAtom         (PTRef tr)      const { return hasSortBool(tr) && isVar(tr); }
    // Check if term is an uninterpreted predicate.
    virtual bool isUP              (PTRef)         const;
    virtual bool isUF              (PTRef)         const;
    virtual bool isUF              (SymRef)        const;

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
    bool        isFalse(PTRef tr)  const { return isFalse(getPterm(tr).symb()); }
    bool        isDistinct(SymRef sr) const { return sr == getSym_distinct(); }
    bool        isDistinct(PTRef tr) const { return isDistinct(getPterm(tr).symb()); }
    bool        isIff(SymRef sr) const { return sr == getSym_eq(); }
    bool        isIff(PTRef tr) const { return isIff(getPterm(tr).symb()); }

    bool        isLit(PTRef tr) const;


    bool        hasSortBool(PTRef tr) const { return sym_store[getPterm(tr).symb()].rsort() == sort_BOOL; }
    bool        hasSortBool(SymRef sr) const { return sym_store[sr].rsort() == sort_BOOL; }
    bool        hasSortInt (PTRef tr) const { return false; }


    // Return the corresponding equivalence term if yes,
    // PTRef_Undef otherwise.
    PTRef       lookupUPEq         (PTRef tr);

    // Returns an equality over args if term store contains one, otherwise returns PTRef_Undef.
    // args is sorted before lookup, but not simplified otherwise
    PTRef       hasEquality        (vec<PTRef>& args);
    // Override for different logics...
    bool        declare_sort_hook  (SRef sr);
    inline bool isPredef           (string&)        const { return false; };

    // Simplify an equality.  TODO: See if this could be combined with
    // simplifyTree
    bool simplifyEquality(PtChild& ptc, bool simplify);
    void simplifyDisequality(PtChild& ptc, bool simplify = true);
    // Simplify a term tree.  Return l_True, l_False, or l_Undef, if
    // simplification resulted in constant true or fale, or neither,
    // respectively
    lbool       simplifyTree       (PTRef tr, PTRef& root_out);

    PTRef       resolveTerm        (const char* s, vec<PTRef>& args, char** msg);
    // XXX There's a need for non msg giving version
    virtual PTRef       insertTerm         (SymRef sym, vec<PTRef>& terms, char** msg);

    // Top-level equalities based substitutions
    void collectFacts(PTRef root, vec<PtAsgn>& facts);
    bool varsubstitute(PTRef& root, Map<PTRef,PtAsgn,PTRefHash>& substs, PTRef& tr_new);  // Do the substitution.  Return true if at least one substitution was done, and false otherwise.
    virtual lbool retrieveSubstitutions(vec<PtAsgn>& facst, Map<PTRef,PtAsgn,PTRefHash>& substs);

    class SubstNode {
        Logic& logic;
        int procChild;
      public:
        int index;
        int lowlink;
        NStatus status;
        PTRef tr;
        vec<PTRef> children;
        vec<SubstNode*> child_nodes;
        SubstNode* parent;
        SubstNode(PTRef tr, PTRef target, SubstNode* parent, Logic& l) : logic(l), procChild(0), index(-1), lowlink(-1), status(ns_unseen), tr(tr), parent(parent) {
            l.getVars(target, children);
            sort(children);
            int i, j;
            PTRef p = PTRef_Undef;
            for (i = j = 0; i < children.size(); i++)
                if (children[i] != p)
                    p = children[j++] = children[i];
            children.shrink(i-j);
        }
        SubstNode* getNextChild() {
            for (; procChild < child_nodes.size(); procChild++) {
                if (child_nodes[procChild] != NULL)
                    return child_nodes[procChild++];
            }
            return NULL;
        }
        void updateLowlink(int i) { lowlink = lowlink < i ? lowlink : i; }
    };

    class TarjanAlgorithm {
        vec<SubstNode*> controlStack;
        vec<SubstNode*> tarjanStack;
        Logic& logic;
        int index;
        void addNode(SubstNode* n) {
            n->index = index;
            n->lowlink = index;
            index++;
            controlStack.push(n);
            tarjanStack.push(n);
            n->status = ns_inStack;
        }
      public:
        TarjanAlgorithm(Logic& l) : logic(l), index(0) {}
        void getLoops(SubstNode* startNode, vec<vec<PTRef> >& loops) {
            addNode(startNode);
            while (controlStack.size() > 0) {
                SubstNode* n = controlStack.last();
                SubstNode* c = n->getNextChild();
                if (c != NULL) {
                    if (c->status == ns_unseen)
                        addNode(c);
                    else if (c->status == ns_inStack)
                        n->updateLowlink(c->index);
                } else {
                    controlStack.pop();
                    if (controlStack.size() > 0)
                        controlStack.last()->updateLowlink(n->lowlink);
                    if (n->lowlink == n->index) {
                        // Start a new SCC
                        vec<PTRef> scc;
                        SubstNode* w = NULL;
                        do {
                            w = tarjanStack.last(); tarjanStack.pop();
                            w->status = ns_complete;
                            scc.push(w->tr);
                        } while (w != n);
                        if (scc.size() > 1) {
                            loops.push();
                            for (int i = scc.size()-1; i >= 0; i--)
                                loops.last().push(scc[i]);
                        }
                    }
                }
            }
        }
    };

    void getVars(PTRef, vec<PTRef>&) const;
    void breakSubstLoops(Map<PTRef,PtAsgn,PTRefHash>& substs);

    bool contains(PTRef x, PTRef y);  // term x contains an occurrence of y

    PTRef learnEqTransitivity(PTRef); // Learn limited transitivity information

    virtual void serializeLogicData(int*& logicdata_buf) const;
    virtual void deserializeLogicData(const int* logicdata_buf);

    void        serializeTermSystem(int*& termstore_buf, int*& symstore_buf, int*& idstore_buf, int*& sortstore_buf, int*& logicdata_buf) const;
    void        deserializeTermSystem(const int* termstore_buf, const int* symstore_buf, const int* idstore_buf, const int* sortstore_buf, const int* logicdata_buf);

    virtual char* printTerm_       (PTRef tr, bool l);
    char*       printTerm          (PTRef tr)         { return printTerm_(tr, false); }
    char*       printTerm          (PTRef tr, bool l) { return printTerm_(tr, l); }
    char*       printSym           (SymRef sr) const;

    void  purify           (PTRef r, PTRef& p, lbool& sgn) const
        {p = r; sgn = l_True; while (isNot(p)) { sgn = sgn^1; p = getPterm(p)[0]; }}

#ifdef PEDANTIC_DEBUG
    void compareSymStore(SymStore& other) { sym_store.compare(other); }
    void compareIdStore(IdentifierStore& other) {}
    void compareSortStore(SStore& other) { }
    void compareTermStore(PtStore& other) { }// term_store.compare(other); }
#endif

    //partitions:
    bool assignPartition(const char* pname, PTRef pref, char** msg)
    {
        return term_store.assignPartition(pname, pref, msg);
    }

    bool assignPartition(PTRef pref, char** msg)
    {
        assertions.push(pref);
        return term_store.assignPartition(pref, msg);
    }

    bool canInterpolate()
    {
#ifdef PRODUCE_PROOF
        return config.produce_inter() && assertions.size() >= 2;
#else
        return false;
#endif //PRODUCE_PROOF
    }


#ifdef PRODUCE_PROOF
    void setIPartitionsIte(PTRef pref);
    ipartitions_t& getClauseClassMask(CRef l) { return clause_class[l]; }
    ipartitions_t& getVarClassMask(Var l) { return var_class[l]; }
    void addClauseClassMask(CRef l, const ipartitions_t& toadd);
    void addVarClassMask(Var l, const ipartitions_t& toadd);
    vec<PTRef>& getAssertions() { return assertions; }
    unsigned getNofPartitions() { return assertions.size(); }
    //TODO: make this better
    bool isAssertion(PTRef pref)
    {
        for (int i = 0; i < assertions.size(); ++i)
            if (assertions[i] == pref)
                return true;
        return false;
    }
    bool isAssertionSimp(PTRef pref)
    {
        for (int i = 0; i < assertions_simp.size(); ++i)
            if (assertions_simp[i] == pref)
                return true;
        return false;
    }
    int assertionIndex(PTRef pref)
    {
        for (int i = 0; i <  assertions.size(); ++i)
            if (assertions[i] == pref)
                return i;
        return -1;
    }
#endif
    // Statistics
    int subst_num; // Number of substitutions

    void collectStats(PTRef, int& n_of_conn, int& n_of_eq, int& n_of_uf);

	inline int     verbose                       ( ) const { return config.verbosity(); }
};

#endif // LOGIC_H

