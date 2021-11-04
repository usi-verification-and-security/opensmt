/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso

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

#ifndef EGRAPH_H
#define EGRAPH_H

// FIXME: make as configure option
#define MORE_DEDUCTIONS 0

#include "Timer.h"
#include "SStore.h"
#include "EnodeStore.h"
#include "Enode.h"
#include "TSolver.h"
#include "SymStore.h"
#include "PtStore.h"
#include "Explainer.h"

#ifdef PEDANTIC_DEBUG
#include "GCTest.h"
#endif

#include <unordered_set>

class UFSolverStats: public TSolverStats
{
    public:
        opensmt::OSMTTimeVal egraph_asrt_timer;
        opensmt::OSMTTimeVal egraph_backtrack_timer;
        opensmt::OSMTTimeVal egraph_explain_timer;
        int num_eq_classes;
        UFSolverStats() : num_eq_classes(0) {}
        void printStatistics(ostream& os)
        {
            os << "; -------------------------" << endl;
            os << "; STATISTICS FOR EUF SOLVER" << endl;
            os << "; -------------------------" << endl;
            TSolverStats::printStatistics(os);
            os << "; egraph time..............: " << egraph_asrt_timer.getTime() << " s\n";
            os << "; backtrack time...........: " << egraph_backtrack_timer.getTime() << " s\n";
            os << "; explain time.............: " << egraph_explain_timer.getTime() << " s\n";
            os << "; # eq classes at the end..: " << num_eq_classes << "\n";
        }
};

/*
 * Holds parents of a congruence class of terms: for a congruence class c its UseVector contains all terms p such that
 * some child of p belongs to c.
 * Moreover, if p's index in UseVector is i then p.getIndex(t) returns i for p's child t.
 */
class UseVector {
    /* First two bits represent tag: 00 - valid entry, 01 - marked entry, 11 - empty entry
     * In case of valid and marked entry, the data is ERef, in case of empty entry, the data is next free entry.
     * This data structure is a vector possibly containing a free list inside
     */
    struct Entry {
    private:
        uint32_t data;
    public:
        static const uint32_t VALID_MASK = 0x00;  // 00
        static const uint32_t MARKED_MASK = 0x01; // 01
        static const uint32_t FREE_MASK = 0x03;   // 11
        static const uint32_t TAG_MASK = 0x03;    // bit mask to get the two least significant bits
        static const uint32_t FREE_ENTRY_LIST_GUARD = (static_cast<uint32_t>(-1)) >> 2;

        // MB: This packing tag and data together means that the value of ERef is restricted to 2^30.
        // This is not an issue for the current benchmarks we are dealing with
        explicit Entry(ERef e): data{e.x << 2} { }
        explicit Entry(uint32_t i): data{i << 2} { }
        Entry(int) = delete;
        Entry() : data{0} {}
        inline bool isFree()   const    { return (data & TAG_MASK) == FREE_MASK; }
        inline bool isValid()  const    { return (data & TAG_MASK) == VALID_MASK; }
        inline bool isMarked() const    { return (data & TAG_MASK) == MARKED_MASK; }
        inline void mark()              { assert(isValid()); data &= ~TAG_MASK; data |= MARKED_MASK; assert(isMarked()); }
        inline void unmark()            { assert(isMarked()); data &= ~TAG_MASK; assert(isValid()); }
        inline void free()              { data |= FREE_MASK; }
        inline uint32_t getData()   const    { return data >> 2;}
    };
    static_assert(sizeof(Entry) == 4, "Entry is not of expected size!");
    std::vector<Entry> data;
    uint32_t free; // pointer to head of a free list, FREE_ENTRY_LIST_GUARD means no free list
    uint32_t nelems; // the real number of elements;

    using iterator = decltype(data)::iterator;
    using const_iterator = decltype(data)::const_iterator;

public:
    UseVector() : data{}, free{Entry::FREE_ENTRY_LIST_GUARD}, nelems{0}
    {}

    uint32_t size() const { return nelems; }

    uint32_t addParent(ERef parent);

    void clearEntryAt(int index);

    void markEntry(Entry& entry);
    void unMarkEntry(Entry& entry);

    iterator begin() { return data.begin(); }
    iterator end() { return data.end(); }
    const_iterator begin() const { return data.cbegin(); }
    const_iterator end() const { return data.cend(); }

    static Entry erefToEntry(ERef e) {
        assert(e.x >> 30 == 0);
        return Entry(e);
    }

    static ERef entryToERef(Entry e) {
        assert(e.isValid());
        uint32_t val = e.getData();
        return ERef{val};
    }

    static uint32_t freeEntryToIndex(Entry e) {
        assert(e.isFree());
        uint32_t val = e.getData();
        return val;
    }

    static Entry indexToFreeEntry(uint32_t index) {
        assert(index >> 30 == 0);
        Entry ret(index);
        ret.free();
        return ret;
    }

    const Entry& operator[](unsigned index) const { assert(index < data.size()); return data[index]; }
private:
    uint32_t getFreeSlotIndex();
};

class Egraph : public TSolver {
protected:
    Logic & logic;
    enum class ExplainerType {
        CLASSIC, INTERPOLATING
    };
    std::unique_ptr<Explainer> explainer;
private:
    /*
     * fields and methods related to parent vectors
     */
    //***************************************************************************************************************
    std::vector<UseVector> parents;

    void addToUseVectors(ERef);
    void updateUseVectors(PTRef);

    void removeFromUseVectorsExcept(ERef parent, CgId cgid);
    void removeFromUseVectors(ERef parent);

    unsigned getParentsSize(ERef ref) {
        assert(getEnode(ref).getCid() < parents.size());
        return parents[getEnode(ref).getCid()].size();
    }

    bool childDuplicatesClass(ERef parent, uint32_t childIndex);

    //***************************************************************************************************************
    Map<PTRef, ERef, PTRefHash> boolTermToERef;

    ELAllocator forbid_allocator;

    EnodeStore enode_store;

    bool isValid(PTRef tr) override { return logic.isUFEquality(tr) || logic.isUP(tr) || logic.isDisequality(tr); }
    bool isEffectivelyEquality(PTRef tr) const;
    bool isEffectivelyUP(PTRef tr) const;
    bool isEffectivelyDisequality(PTRef tr) const;

    double fa_garbage_frac;

    UFSolverStats tsolver_stats;

    class Values {
        Map<ERef, ERef, ERefHash> values;
        Map<ERef, int, ERefHash> valueERefToInt;
        int valueCounter;
    public:
        Values() : valueCounter(0) {}
        void addValue(ERef t, ERef v) { if (values.has(t)) return; values.insert(t, v); if (not valueERefToInt.has(v)) { valueERefToInt.insert(v, valueCounter++); } }
        bool hasValue(ERef er) const { return values.has(er); }
        ERef getValue(ERef er) const { assert(values.has(er)); return values[er]; }
        int getValueIndex(ERef er) const { assert(valueERefToInt.has(er)); return valueERefToInt[er]; }
    };

    std::unique_ptr<Values> values;

    static const char * s_val_prefix;
    static const char * s_const_prefix;
    static const char * s_any_prefix;
    static const char * s_val_true;
    static const char * s_val_false;

protected:
    Egraph(SMTConfig & c, Logic & l, ExplainerType explainerType);

public:
    Egraph(SMTConfig & c, Logic & l);

    virtual ~Egraph() {
        backtrackToStackSize(0);
#ifdef STATISTICS
        tsolver_stats.printStatistics(std::cerr);
#endif // STATISTICS
    }

    void clearSolver() override { clearModel(); } // Only clear the possible computed values

    void print(ostream &) override { return; }

protected:
    inline Enode & getEnode(ERef er) { return enode_store[er]; }

private:
    ERef termToERef(PTRef p) { return enode_store.getERef(p); }

public:
    inline const Enode & getEnode(ERef er) const { return enode_store[er]; }

    PTRef ERefToTerm(ERef er) const { return getEnode(er).getTerm(); }

    bool isConstant(ERef er) const {
        return logic.isConstant(getEnode(er).getTerm());
    }

#ifdef STATISTICS
    void printMemStats (ostream &);
#endif
    void computePolarities (ERef);

    //===========================================================================
    // Public APIs for Theory Combination with DTC

    void    gatherInterfaceTerms     (ERef);
    int     getInterfaceTermsNumber  ();
    ERef    getInterfaceTerm         (const int);
    bool    isRootUF                 (ERef);
    ERef    canonizeDTC              (ERef, bool = false);

    Logic& getLogic() override { return logic; }

    void addTheoryFunctionEvaluation(ModelBuilder & modelBuilder, PTRef tr, ERef er) const;
public:

  //===========================================================================
  // Public APIs for Egraph Core Solver

    bool       assertLit               (PtAsgn) override;
    void       pushBacktrackPoint      () override;                 // Push a backtrack point
    void       popBacktrackPoint       () override;                 // Backtrack to last saved point
    PTRef      getSuggestion           ();                          // Return a suggested literal based on the current state
    lbool      getPolaritySuggestion   (PTRef);                     // Return a suggested polarity for a given literal
    void       getConflict             (bool, vec<PtAsgn>&) override;// Get explanation
    TRes       check                   (bool) override { return TRes::SAT; }// Check satisfiability
    void       computeModel            () override;
    void       fillTheoryFunctions     (ModelBuilder & modelBuilder) const override;
    void       clearModel              ();
    PTRef      getAbstractValueForERef (ERef er, SRef sr) const;
    void       splitOnDemand           (vec<PTRef> &, int) {};       // Splitting on demand modulo equality


#if MORE_DEDUCTIONS
  bool                deduceMore              ( vector< ERef > & );
#endif

private:

  //
  // Defines the set of operations that can be performed and that should be undone
  //
    typedef enum {      // These constants are stored on undo_stack_oper when
      CONS            // An undoable cons is done
    , MERGE           // A merge is done
    , DISEQ           // A negated equality is asserted
    , DIST            // A distinction is asserted
    , EXPL            // Explanation added
    , SET_DYNAMIC     // Dynamic info was set
    , SET_POLARITY    // A polarity of a PTRef was set
    , UNDEF_OP        // A dummy value for default constructor
    #if MORE_DEDUCTIONS
    , ASSERT_NEQ
    #endif
    } oper_t;

      class Undo {
        public:
          oper_t oper;
          union arg_t { PTRef ptr; ERef er; } arg;
          Undo(oper_t o, PTRef r) : oper(o) { arg.ptr = r; }
          Undo(oper_t o, ERef r)  : oper(o) { arg.er = r; }
          Undo()         : oper(UNDEF_OP)   { arg.ptr = PTRef_Undef; }
    #ifdef VERBOSE_EUF
          ERef merged_with;
          PTRef bool_term;
    #endif
      };


    //===========================================================================
    // Private Routines for Core Theory Solver

    //
    // Asserting literals
    //
public:
    bool      addDisequality      ( PtAsgn );
    bool      addEquality         ( PtAsgn );
    bool      addTrue             ( PTRef );
    bool      addFalse            ( PTRef );

    void      declareAtom(PTRef) override;
    // Non-recursive declare term
    void      declareTerm         (PTRef);

private:

    std::unordered_set<PTRef, PTRefHash> declared;
    void declareTermRecursively(PTRef);

    bool    assertEq        (PTRef, PTRef, PtAsgn);               // Asserts an equality
    bool    assertEq        (ERef, ERef, PtAsgn);                 // Called by the above
    bool    assertNEq       (PTRef, PTRef, const Expl &r);        // Asserts a negated equality
    bool    assertNEq       (ERef, ERef, const Expl &r);          // Called by the above
    bool    assertDist      ( PTRef, PtAsgn);                     // Asserts a distinction
    //
    // Backtracking
    //
    void    backtrackToStackSize ( size_t );                      // Backtrack to a certain operation
    //
    // Congruence closure main routines
    //

    bool    unmergeable     ( ERef, ERef, Expl& ) const;        // Can two nodes be merged ?
    void    merge           ( ERef, ERef, PtAsgn );               // Merge two nodes
    bool    mergeLoop       ( PtAsgn reason );                    // Merge loop
    void    deduce          ( ERef, ERef, PtAsgn );               // Deduce from merging of two nodes (record the reason)
    void    undoMerge       ( ERef );                             // Undoes a merge
    void    undoDisequality ( ERef );                             // Undoes a disequality
    void    undoDistinction ( PTRef );                            // Undoes a distinction


    vec<ERef>                 pending;                          // Pending merges
    vec<Undo>                 undo_stack_main;                  // Keeps track of terms involved in operations

    void doExplain(ERef, ERef, PtAsgn);                            // Explain why the Enodes are equivalent when PtAsgn says it should be different
    void explainConstants(ERef, ERef);

    //============================================================================
    // Memory management for forbid allocator
    void faGarbageCollect();
    inline void checkFaGarbage(void) { return checkFaGarbage(fa_garbage_frac); }
    inline void checkFaGarbage(double gf) {
        if (forbid_allocator.wasted() > forbid_allocator.size() * gf)
            faGarbageCollect();
    }
    void relocAll(ELAllocator&);
    //============================================================================

    //===========================================================================
    // Debugging routines - Implemented in EgraphDebug.C
public:
    char* printEqClass               ( PTRef tr ) const;
    char* printDistinctions          ( PTRef tr ) const;
    char* printExplanation           ( PTRef tr ) { char* tmp; asprintf(&tmp, "%s", printExplanationTreeDotty(enode_store.getERef(tr)).c_str()); return tmp; }
private:
    std::string toString                 (ERef er) const;
public:
    string printExplanationTreeDotty(ERef);
private:
    const string printDistinctionList( ELRef, ELAllocator& ela, bool detailed = true );
    void checkForbidReferences       ( ERef );
    void checkRefConsistency         ( );
    // Helper methods
    void mergeForbidLists(ERef to, const Enode & from);
    void unmergeForbidLists(ERef to, const Enode & from);
    void mergeDistinctionClasses(Enode & to, const Enode & from);
    void unmergeDistinctionClasses(Enode & to, const Enode & from);
    void mergeEquivalenceClasses(ERef newroot, ERef oldroot);
    void unmergeEquivalenceClasses(ERef newroot, ERef oldroot);
    void processParentsBeforeMerge(ERef mergedRoot);
    void processParentsAfterMerge(ERef mergedRoot);
    void processParentsBeforeUnMerge(ERef oldroot);
    void processParentsAfterUnMerge(ERef oldroot);

#ifdef STATISTICS
    void printStatistics ( ofstream & );
#endif
};

#endif
