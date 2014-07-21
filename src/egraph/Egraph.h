/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2010, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#ifndef EGRAPH_H
#define EGRAPH_H

// FIXME: make as configure option
#define MORE_DEDUCTIONS 0

#include "SStore.h"
#include "EnodeStore.h"
#include "Enode.h"
#include "TSolver.h"
#include "SymStore.h"
#include "PtStore.h"
#include "Logic.h"
// For debugging
#include "TermMapper.h"
//#include "SigTab.h"
//#include "SplayTree.h"

#ifdef PEDANTIC_DEBUG
#include "GCTest.h"
#endif

#ifdef PRODUCE_PROOF
#include "UFInterpolator.h"
#endif


class Egraph : public CoreTSolver
{
private:
  SStore &      sort_store;
  SymStore &    sym_store;
  PtStore&      term_store;
  Logic&        logic;
  TermMapper&   tmap;
#ifdef CUSTOM_EL_ALLOC
  ELAllocator   forbid_allocator;
#endif
  EnodeStore    enode_store;
  ERef          ERef_Nil;

  PTRef         Eq_FALSE; // will be set to (= true false) in constructor

#ifndef TERMS_HAVE_EXPLANATIONS
  // Explanations
  Map<PTRef,PTRef,PTRefHash,Equal<PTRef> >  expParent;
  Map<PTRef,int,PTRefHash,Equal<PTRef> >    expTimeStamp;
  Map<PTRef,int,PTRefHash,Equal<PTRef> >    expClassSize;
  Map<PTRef,PtAsgn,PTRefHash,Equal<PTRef> > expReason;
  Map<PTRef,PTRef,PTRefHash,Equal<PTRef> >  expRoot;
#endif

  Map<PTRef,lbool,PTRefHash>    polarityMap;

  double fa_garbage_frac;

public:
  SimpSMTSolver* solver; // for debugging only

  Egraph( SMTConfig & c
        , SStore & s, SymStore& syms, PtStore& terms, Logic& l, TermMapper& term_map )
      : CoreTSolver        ( 0, "EUF Solver", c )
      , sort_store         ( s )
      , sym_store          ( syms )
      , term_store         ( terms )
      , logic              ( l )
      , tmap               ( term_map )
#if defined(PEDANTIC_DEBUG) && defined(CUSTOM_EL_ALLOC)
      , enode_store        ( sym_store, term_store, forbid_allocator )
#else
      , enode_store        ( sym_store, term_store )
#endif
      , ERef_Nil           ( enode_store.get_Nil() )
      , fa_garbage_frac    ( 0.5 )
      , active_dup1        ( false )
      , active_dup2        ( false )
      , dup_count1         ( 0 )
      , dup_count2         ( 0 )
      , active_dup_map1    ( false )
      , active_dup_map2    ( false )
      , dup_map_count1     ( 0 )
      , dup_map_count2     ( 0 )
      , congruence_running ( false )
      , theoryInitialized  ( false )
      , time_stamp         ( 0 )
//      , use_gmp            ( false )
#ifdef PRODUCE_PROOF
      , iformula           ( 1 )
      , cgraph_            ( new CGraph( *this, config ) )
      , cgraph             ( *cgraph_ )
      , automatic_coloring ( false )
#endif
  {
    // For the uninterpreted predicates to work we need to have
    // two special terms true and false, and an asserted disequality
    // true != false

    // This is for the enode store
    // XXX These guys should be defined through the same interface every
    // other term is defined.  This is probably declareTerm()
    ERef ers_true  = enode_store.addSymb(logic.getSym_true());
    ERef ers_false = enode_store.addSymb(logic.getSym_false());
    PTRef ptr_new_true  = enode_store.addTerm(ers_true, ERef_Nil,
                            logic.getTerm_true());
    PTRef ptr_new_false = enode_store.addTerm(ers_false, ERef_Nil,
                            logic.getTerm_false());

    assert(ptr_new_true  == logic.getTerm_true());
    assert(ptr_new_false == logic.getTerm_false());
#ifndef TERMS_HAVE_EXPLANATIONS
    expReason.insert(ptr_new_true, PtAsgn(PTRef_Undef, l_Undef));
    expReason.insert(ptr_new_false, PtAsgn(PTRef_Undef, l_Undef));
    expParent.insert(ptr_new_true, PTRef_Undef);
    expParent.insert(ptr_new_false, PTRef_Undef);
    expRoot.insert(ptr_new_true, ptr_new_true);
    expRoot.insert(ptr_new_false, ptr_new_false);
    expClassSize.insert(ptr_new_true, 1);
    expClassSize.insert(ptr_new_false, 1);
    expTimeStamp.insert(ptr_new_true, 0);
    expTimeStamp.insert(ptr_new_false, 0);
#endif
    PTRef t = logic.getTerm_true();
    PTRef f = logic.getTerm_false();
    enode_store[t].setConstant(t);
    enode_store[f].setConstant(f);

    enode_store.ERef_True  = enode_store.termToERef[t];
    enode_store.ERef_False = enode_store.termToERef[f];
    // add the term (= true false) to term store
    vec<PTRef> tmp;
    tmp.push(logic.getTerm_true());
    tmp.push(logic.getTerm_false());
    const char* msg;
    PTRef neq = logic.insertTerm(logic.getSym_eq(), tmp, &msg);
    assert(neq != PTRef_Undef);
    assertNEq(logic.getTerm_true(), logic.getTerm_false(), PtAsgn(neq, l_False));
    Eq_FALSE = neq;
  }

    ~Egraph( ) {
        backtrackToStackSize( 0 );
#ifdef STATISTICS
        // TODO added for convenience
        if ( config.produceStats() ) {
            config.getStatsOut( ) << "; -------------------------" << endl;
            config.getStatsOut( ) << "; STATISTICS FOR EUF SOLVER" << endl;
            config.getStatsOut( ) << "; -------------------------" << endl;
            tsolver_stats.printStatistics( config.getStatsOut( ) );
        }

        if ( config.print_stats ) {
            cerr << "; -------------------------" << endl;
            cerr << "; STATISTICS FOR EUF SOLVER" << endl;
            cerr << "; -------------------------" << endl;
            tsolver_stats.printStatistics( cerr );
        }
#endif
        //
        // Delete Ordinary Theory Solvers
        //
        // TODO added for convenience
        for ( unsigned i = 1 ;
              ( config.produceStats() || config.print_stats ) && i < tsolvers.size_( ) ;
              i ++ ) {
#ifdef STATISTICS
//            if ( config.produceStats() ) {
//                config.getStatsOut( ) << "# -------------------------" << endl;
//                config.getStatsOut( ) << "# STATISTICS FOR " << tsolvers[ i ]->getName( ) << endl;
//                config.getStatsOut( ) << "# -------------------------" << endl;
//                assert( tsolvers_stats[ i ] );
//                tsolvers_stats[ i ]->printStatistics( config.getStatsOut( ) );
//            }
//            if ( config.print_stats ) {
//                cerr << "# -------------------------" << endl;
//                cerr << "# STATISTICS FOR " << tsolvers[ i ]->getName( ) << endl;
//                cerr << "# -------------------------" << endl;
//                assert( tsolvers_stats[ i ] );
//               tsolvers_stats[ i ]->printStatistics( cerr );
//            }
//            delete tsolvers_stats[ i ];
#endif
            assert( tsolvers[ i ] );
            delete tsolvers[ i ];
        }
        //
        // Delete enodes
        //
        while ( enode_store.id_to_enode.size() != 0 ) {
            ERef er = enode_store.id_to_enode.last();
            if (er != ERef_Undef )
                enode_store.free(er);

            enode_store.id_to_enode.pop();
        }
#ifdef PRODUCE_PROOF
        assert( cgraph_ );
        delete cgraph_;
#endif
    }

    bool  isDeduced(PTRef tr)   const    { return enode_store[tr].isDeduced(); }
    lbool getDeduced(PTRef tr)  const    { return enode_store[tr].getDeduced(); }

    bool  isConstant(ERef er)   const    { return enode_store.ERef_True == er || enode_store.ERef_False == er; }

    void  setPolarity(PTRef tr, lbool p) {
        if (polarityMap.contains(tr)) { polarityMap[tr] = p; }
        else { polarityMap.insert(tr, p); }
#ifdef PEDANTIC_DEBUG
        cerr << "Setting polarity " << logic.printTerm(tr) << endl;
#endif
    }
    lbool getPolarity(PTRef tr)          { return polarityMap[tr]; }
    bool  hasPolarity(PTRef tr)          { if (polarityMap.contains(tr)) { return polarityMap[tr] != l_Undef; } else return false; }
    void  clearPolarity(PTRef tr)        {
        polarityMap[tr] = l_Undef;
#ifdef PEDANTIC_DEBUG
        cerr << "Clearing polarity " << logic.printTerm(tr) << endl;
#endif
    }

    size_t size() const { return enode_store.id_to_enode.size(); };


  //===========================================================================
  // Public APIs for enode construction/destruction

  ERef    getUncheckedAssertions  ( );
  void    setDistinctEnodes       ( vec<ERef> & );

  void    printEnodeList          ( ostream & );
  void    addAssertion            ( ERef );

  void          initializeStore   ( );
#ifndef SMTCOMP
//  inline void   addSubstitution   ( ERef s, ERef t ) { top_level_substs.push_back( make_pair( s, t ) ); }
#endif
  inline void   setTopEnode       ( ERef e )         { assert( e != ERef_Nil ); top = e; }
  inline size_t nofEnodes         ( )                { return enode_store.id_to_enode.size( ); }



  ERef copyEnodeEtypeTermWithCache   ( ERef, bool = false );
  ERef copyEnodeEtypeListWithCache   ( ERef, bool = false );

  ERef canonize                      ( ERef, bool = false );
  ERef maximize                      ( ERef );

#ifdef STATISTICS
  void        printMemStats             ( ostream & );
#endif
  //
  // Fast duplicates checking. Cannot be nested !
  //
  inline void initDup1 ()        { assert( !active_dup1 ); active_dup1 = true; dup_count1 ++; }
  inline void storeDup1(PTRef e) { assert(  active_dup1 ); if (duplicates1.contains(e)) duplicates1[e] = dup_count1; else duplicates1.insert(e, dup_count1); }
  inline bool isDup1   (PTRef e) { assert(  active_dup1 ); return !duplicates1.contains(e) ? false : duplicates1[e] == dup_count1; }
  inline void doneDup1 ()        { assert(  active_dup1 ); active_dup1 = false; }
  //
  // Fast duplicates checking. Cannot be nested !
  //
  inline void initDup2  ( )           { assert( !active_dup2 ); active_dup2 = true; duplicates2.growTo( enode_store.id_to_enode.size( ), dup_count2 ); dup_count2 ++; }
  inline void storeDup2 ( ERef e ) { assert(  active_dup2 ); assert( enode_store[e].getId() < (enodeid_t)duplicates2.size_() ); duplicates2[ enode_store[e].getId( ) ] = dup_count2; }
  inline bool isDup2    ( ERef e ) { assert(  active_dup2 ); assert( enode_store[e].getId() < (enodeid_t)duplicates2.size_() ); return duplicates2[ enode_store[e].getId( ) ] == dup_count2; }
  inline void doneDup2  ( )           { assert(  active_dup2 ); active_dup2 = false; }
  //
  // Fast duplicates checking. Cannot be nested !
  //
  void    initDupMap1  ( );
  void    storeDupMap1 ( ERef, ERef );
  ERef    valDupMap1   ( ERef );
  void    doneDupMap1  ( );

  void    initDupMap2  ( );
  void    storeDupMap2 ( ERef, ERef );
  ERef    valDupMap2   ( ERef );
  void    doneDupMap2  ( );

  void    computePolarities ( ERef );

  void dumpAssertionsToFile ( const char * );
  void dumpHeaderToFile     ( ostream &, logic_t = UNDEF );
  void dumpFormulaToFile    ( ostream &, ERef, bool = false );
  void dumpToFile           ( const char *, ERef );

  //===========================================================================
  // Public APIs for Theory Combination with DTC

  void    gatherInterfaceTerms     ( ERef );
  int     getInterfaceTermsNumber  ( );
  ERef    getInterfaceTerm         ( const int );
  bool    isRootUF                 ( ERef );
  ERef    canonizeDTC              ( ERef, bool = false );
  // Not used but left there
//  bool    isPureUF                 ( Enode * );
//  bool    isPureLA                 ( Enode * );
#ifdef PRODUCE_PROOF
  void    getInterfaceVars         ( Enode *, set< Enode * > & );
#endif

private:

  vec< ERef > interface_terms;
  // Cache for interface terms
//  set< Enode * > interface_terms_cache;
  // Cache for uf terms and la terms
//  set< Enode * > it_uf, it_la;

public:

  //===========================================================================
  // Public APIs for Egraph Core Solver

//  void                initializeTheorySolvers ( SimpSMTSolver * );          // Attaches ordinary theory solvers
  lbool               inform                  ( PTRef ) { return l_True; }   // Inform the solver about the existence of a theory atom
  bool                assertLit               ( PTRef, bool = false ) {return true; } // Assert a theory literal
  void                pushBacktrackPoint      ( );                          // Push a backtrack point
  void                popBacktrackPoint       ( );                          // Backtrack to last saved point
  PtAsgn_reason&      getDeduction            ( );                          // Return an implied node based on the current state
  PTRef               getSuggestion           ( );                          // Return a suggested literal based on the current state
  void                getConflict             ( bool, vec<PtAsgn>& );       // Get explanation
  bool                check                   ( bool );                     // Check satisfiability
//  void                initializeCong          ( Enode * );                  // Initialize congruence structures for a node
#ifndef SMTCOMP
//  void                computeModel            ( );
//  void                printModel              ( ostream & );                // Computes and print the model
#endif
//  inline void         setUseGmp               ( ) { use_gmp = true; }
//  inline bool         getUseGmp               ( ) { return use_gmp; }
  void                splitOnDemand           ( vec<PTRef> &, int ) { };       // Splitting on demand modulo equality
//  void                splitOnDemand           ( ERef, int );                // Splitting on demand
//  bool                checkDupClause          ( ERef, ERef);                // Check if a clause is duplicate
  void                explain                 ( PTRef
                                              , PTRef
                                              , vec<PTRef> & );             // Exported explain
  // Temporary merge, used by array theory to merge indexes
#ifdef PRODUCE_PROOF
  void                tmpMergeBegin           ( ERef, ERef );
  void                tmpMergeEnd             ( ERef, ERef );
#endif

  //===========================================================================
  // Exported function for using egraph as supporting solver

  bool                extAssertLit            ( ERef );                     // Assert a theory literal
  void                extPushBacktrackPoint   ( );                          // Push a backtrack point
  void                extPopBacktrackPoint    ( );                          // Backtrack to last saved point
#if MORE_DEDUCTIONS
  bool                deduceMore              ( vector< ERef > & );
#endif

  bool                isInitialized             ( );

private:

  //===========================================================================
  // Private Routines for enode construction/destruction

//  Snode * sarith1;
//  Snode * sarray;
//  Snode * sindex;
//  Snode * selem;

  //
  // Defines the set of operations that can be performed and that should be undone
  //
  typedef enum {      // These constants are stored on undo_stack_oper when
      SYMB            // A new symbol is created
    , NUMB            // A new number is created
    , CONS            // An undoable cons is done
    , MERGE           // A merge is done
    , INITCONG        // Congruence initialized
    , FAKE_MERGE      // A fake merge for incrementality
    , FAKE_INSERT     // A fake insert for incrementality
    , DISEQ           // A negated equality is asserted
    , DIST            // A distinction is asserted
    , INSERT_STORE    // Inserted in store
    , EXPL            // Explanation added
    , SET_DYNAMIC     // Dynamic info was set
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
#ifdef PEDANTIC_DEBUG
      ERef merged_with;
      PTRef bool_term;
#endif
  };

  /*
  //
  // Handy function to swap two arguments of a list
  //
  inline ERef swapList ( ERef args )
  {
    assert( args != ERef_Undef );
    Enode& en = enode_store[args];
    assert( en.isList() );
    assert( en.getArity() == 2 );
    return enode_store.addList(
            enode_store[en.getCdr()].getCar(),
            enode_store.addList(en.getCar(),
                                ERef_Nil));
  }
  */
  //
  // Related to term creation
  //
//  Enode * insertNumber ( Enode * );                             // Inserts a number
//  void    removeNumber ( Enode * );                             // Remove a number
//  void    insertSymbol ( Enode * );                             // Inserts a symbol
//  void    removeSymbol ( Enode * );                             // Remove a symbol
//  Enode * lookupSymbol ( const char * name );                   // Retrieve a symbol
//  void    insertDefine ( const char *, Enode * );               // Insert a define
//  Enode * lookupDefine ( const char * );                        // Retrieve a define
//  Enode * insertStore  ( const enodeid_t, Enode *, Enode * );   // Insert node into the global store
//  void    removeStore  ( Enode * );                             // Remove a node from the global store
#ifndef SMTCOMP
//  void    evaluateTermRec ( Enode *, Real & );                  // Evaluate node
#endif
  //
  // Related to congruence closure
  //
//  Enode * insertSigTab ( const enodeid_t, Enode *, Enode * );   // For undoable cons only
//  Enode * insertSigTab ( Enode * );                             // For for terms that go in the congruence
//  Enode * lookupSigTab ( Enode * );                             // Retrieve Enode
//  void    removeSigTab ( Enode * );                             // Remove Enode from sig_tab

  bool                        active_dup1;                      // To prevent nested usage
  bool                        active_dup2;                      // To prevent nested usage
  Map<PTRef,int,PTRefHash,Equal<PTRef> >  duplicates1;          // Fast duplicate checking
  vec< int >                  duplicates2;                      // Fast duplicate checking
  int                         dup_count1;                       // Current dup token
  int                         dup_count2;                       // Current dup token
  bool                        active_dup_map1;                  // To prevent nested usage
  bool                        active_dup_map2;                  // To prevent nested usage
  vec< ERef >                 dup_map1;                         // Fast duplicate checking
  vec< int >                  dup_set1;                         // Fast duplicate checking
  vec< ERef >                 dup_map2;                         // Fast duplicate checking
  vec< int >                  dup_set2;                         // Fast duplicate checking
  int                         dup_map_count1;                   // Current dup token
  int                         dup_map_count2;                   // Current dup token
//  map< string, Enode * >      name_to_number;                   // Store for numbers
//  map< string, Enode * >      name_to_symbol;                   // Store for symbols
//  map< string, Enode * >      name_to_define;                   // Store for defines

//  SplayTree< Enode *, Enode::idLessThan > store;                // The actual store
//  SigTab                                  sig_tab;              // (Supposely) Efficient Signature table for congruence closure

//  vector< Enode * >              id_to_enode;                   // Table ENODE_ID --> ENODE
//  vector< int >                  id_to_belong_mask;             // Table ENODE_ID --> ENODE
//  vector< int >                  id_to_fan_in;                  // Table ENODE_ID --> fan in
//  list< Enode * >                assertions;                    // List of assertions
//  vector< Enode * >              cache;                         // Cache simplifications
  ERef                        top;                              // Top node of the formula
//  map< Pair( int ), Enode * >    ext_store;                     // For fast extraction handling
//  vector< Enode * >              se_store;                      // For fast sign extension
//  vector< int >                  id_to_inc_edges;               // Keeps track of how many edges enter an enode
//  bool                           has_ites;                      // True if there is at least one ite
//  set< Enode * >                 variables;                     // List of variables
#ifndef SMTCOMP
//  vector< Pair( Enode * ) >      top_level_substs;              // Keep track of substitutuions in TopLevelProp.C
  bool                           model_computed;                // Has model been computed lately ?
#endif
  bool                           congruence_running;            // True if congruence is running

  //===========================================================================
  // Private Routines for Core Theory Solver

  bool    assertLit_      ( PTRef ) { return true; }             // Assert a theory literal
  //
  // Asserting literals
  //
public:
//  lbool       simplifyAndAddTerms ( PTRef, vec<PtPair>&, vec<PTRef>& );
  lbool       addDisequality      ( PtAsgn );
  lbool       addEquality         ( PtAsgn );
  bool       addTrue             ( PTRef );
  bool       addFalse            ( PTRef );
  // The term to be added, a list to be filled with the ites found, and
  // the nested booleans that should be processed again with the CNF
  // solver
//  lbool       addTerm             ( PTRef, vec<PtPair>&, vec<PTRef>& );
  // Non-recursive declare term
  void        declareTerm         ( PtChild );
  // Recursive declare term
  void        declareTermTree     ( PTRef );
  // Remove redundancies and replace with true if
  // trivial.  Return true if root of the formula is trivially true
  bool        simplifyEquality    ( PtChild&, bool simplify = true );
  void        simplifyDisequality ( PtChild&, bool simplify = true );
private:
  bool    assertEq        ( PTRef, PTRef, PtAsgn );               // Asserts an equality
  bool    assertNEq       ( PTRef, PTRef, PtAsgn );               // Asserts a negated equality
  bool    assertDist      ( PTRef, PtAsgn );                      // Asserts a distinction
  //
  // Backtracking
  //
  void    backtrackToStackSize ( size_t );                      // Backtrack to a certain operation
  //
  // Congruence closure main routines
  //
  bool    unmergeable     ( ERef, ERef, PtAsgn& );              // Can two nodes be merged ?
  void    merge           ( ERef, ERef, PtAsgn );               // Merge two nodes
  bool    mergeLoop       ( PtAsgn reason );                    // Merge loop
  void    deduce          ( ERef, ERef, PtAsgn );               // Deduce from merging of two nodes (record the reason)
  void    undoMerge       ( ERef );                             // Undoes a merge
  void    undoDisequality ( ERef );                             // Undoes a disequality
  void    undoDistinction ( PTRef );                            // Undoes a distinction
  //
  // Explanation routines and data
  //
  void     expExplain           ( );                            // Main routine for explanation
#ifdef PRODUCE_PROOF
  void     expExplain           ( PTRef, PTRef, PTRef );        // Enqueue equality and explain
#else
  void     expExplain           ( PTRef, PTRef );               // Enqueue equality and explain
#endif
  void     expStoreExplanation  ( ERef, ERef, PtAsgn );         // Store the explanation for the merge
  void     expExplainAlongPath  ( PTRef, PTRef );               // Store explanation in explanation
  void     expEnqueueArguments  ( PTRef, PTRef );               // Enqueue arguments to be explained
  void     expReRootOn          ( PTRef );                      // Reroot the proof tree on x
  void     expUnion             ( PTRef, PTRef );               // Union of x and y in the explanation
  PTRef    expFind              ( PTRef );                      // Find for the eq classes of the explanation
  PTRef    expHighestNode       ( PTRef );                      // Returns the node of the eq class of x that is closest to the root of the explanation tree
  PTRef    expNCA               ( PTRef, PTRef );               // Return the nearest common ancestor of x and y
  void     expRemoveExplanation ( );                            // Undoes the effect of expStoreExplanation
  void     expCleanup           ( );                            // Undoes the effect of expExplain

  inline const char * logicStr ( logic_t l )
  {
         if ( l == EMPTY )     return "EMPTY";
    else if ( l == QF_UF )     return "QF_UF";
    else if ( l == QF_BV )     return "QF_BV";
    else if ( l == QF_RDL )    return "QF_RDL";
    else if ( l == QF_IDL )    return "QF_IDL";
    else if ( l == QF_LRA )    return "QF_LRA";
    else if ( l == QF_LIA )    return "QF_LIA";
    else if ( l == QF_UFRDL )  return "QF_UFRDL";
    else if ( l == QF_UFIDL )  return "QF_UFIDL";
    else if ( l == QF_UFLRA )  return "QF_UFLRA";
    else if ( l == QF_UFLIA )  return "QF_UFLIA";
    else if ( l == QF_UFBV )   return "QF_UFBV";
    else if ( l == QF_AX )     return "QF_AX";
    else if ( l == QF_AXDIFF ) return "QF_AXDIFF";
    else if ( l == QF_BOOL )   return "QF_BOOL";
    return "";
  }

  bool                        theoryInitialized;                // True if theory solvers are initialized
  bool                        state;                            // the hell is this ?
  set< enodeid_t >            initialized;                      // Keep track of initialized nodes
  map< enodeid_t, lbool >     informed;                         // Keep track of informed nodes
  vec< ERef >                 pending;                          // Pending merges
  vec< Undo >                 undo_stack_main;                  // Keeps track of terms involved in operations
//  vec< oper_t >               undo_stack_oper;                  // Keeps track of operations
  vec< PtAsgn >               explanation;                      // Stores explanation

#if MORE_DEDUCTIONS
  vec< ERef>                  neq_list;
#endif

  vec< PTRef >                exp_pending;                      // Pending explanations
  vec< PTRef >                exp_undo_stack;                   // Keep track of exp_parent merges
  vec< PTRef >                exp_cleanup;                      // List of nodes to be restored
  int                         time_stamp;                       // Need for finding NCA
  int                         conf_index;                       // Index of theory solver that caused conflict

//  Real                        rescale_factor;                   // Rescale factor for DL
//  long                        rescale_factor_l;                 // Rescale factor for DL
//  bool                        use_gmp;                          // Do we have to use gmp?

  void    initializeCongInc ( ERef );                           // Initialize a node in the congruence at runtime
  void    initializeAndMerge( ERef );                           // Initialize a node in the congruence at runtime
  ERef    uCons             ( ERef, ERef );                     // Undoable cons - To create dynamic terms
  void    undoCons          ( ERef );                           // Undoes a cons

#ifdef CUSTOM_EL_ALLOC
  //============================================================================
  // Memory management for forbid allocator
  void faGarbageCollect();
  inline void checkFaGarbage(void) { return checkFaGarbage(fa_garbage_frac); }
  inline void checkFaGarbage(double gf) {
    if (forbid_allocator.wasted() > forbid_allocator.size() * gf)
        faGarbageCollect(); }
  void relocAll(ELAllocator&);
#endif
  //============================================================================

#ifdef BUILD_64
  hash_set< enodeid_pair_t >     clauses_sent;
#else
  hash_set< Pair( enodeid_t ) >  clauses_sent;
#endif

#ifdef PRODUCE_PROOF
  //===========================================================================
  // Interpolation related routines - Implemented in EgraphDebug.C

public:

  inline void     setAutomaticColoring    ( ) { assert( !automatic_coloring ); automatic_coloring = true; }
  inline unsigned getNofPartitions        ( ) { return iformula - 1; }

  Enode *         getInterpolants         ( logic_t & );     
  Enode *         getNextAssertion        ( );
  Enode *         expandDefinitions       ( Enode * );
  void            addDefinition           ( Enode *, Enode * );
  void            maximizeColors          ( );
  void            finalizeColors          ( Enode *, const ipartitions_t & );

private:

  inline void     formulaToTag     ( Enode * e ) { formulae_to_tag.push_back( e ); }

  void            addIFormula      ( );
  void            tagIFormulae     ( const ipartitions_t & );
  void            tagIFormulae     ( const ipartitions_t &, vector< Enode * > & );
  void            tagIFormula      ( Enode *, const ipartitions_t & );

  void            scanForDefs      ( Enode *, set< Enode * > & );
  Enode *         substitute       ( Enode *, map< Enode *, Enode * > & );

  unsigned                iformula;                  // Current formula id
  vector< Enode * >       formulae_to_tag;           // Formulae to be tagged
  vector< uint64_t >      id_to_iformula;            // From enode to iformula it belongs to
  CGraph *                cgraph_;                   // Holds congrunce graph and compute interpolant 
  CGraph &                cgraph;                    // Holds congrunce graph and compute interpolant 
  bool                    automatic_coloring;        // Set automatic node coloring
  vector< Enode * >       idef_list;                 // Definition list in rev chron order
  map< Enode *, Enode * > idef_map;                  // Def to term map
#endif

  //===========================================================================
  // Debugging routines - Implemented in EgraphDebug.C

//  string printEqClass              ( ERef );
public:
  char* printEqClass               ( PTRef tr ) const;
  char* printDistinctions          ( PTRef tr ) const;
private:
  bool   isEqual                   (PTRef, PTRef) const;
  string printExplanation          ( );
  string printExplanationTree      ( PTRef );
public:
  string printExplanationTreeDotty ( PTRef );
private:
#ifdef CUSTOM_EL_ALLOC
  const string printDistinctionList( ELRef, ELAllocator& ela, bool detailed = true );
#else
  const string printDistinctionList( Elist* );
#endif
  void checkForbidReferences       ( ERef );
  void checkRefConsistency         ( );
  string printCbeStructure         ( );
  string printCbeStructure         ( ERef, set< int > & );
  string printParents              ( ERef );

#if PEDANTIC_DEBUG
public:
  const char* printUndoTrail     ( );
  const char* printAsrtTrail     ( );
private:
  bool checkParents              ( ERef );
  bool checkInvariants           ( );
//  bool checkInvariantFLS         ( );
  bool checkInvariantSTC         ( ) { return enode_store.checkInvariants(); }
  bool checkExp                  ( );
  bool checkExpTree              ( PTRef );
  bool checkExpReachable         ( PTRef, PTRef );
#endif
  bool checkStaticDynamicTable   ( );

#ifdef STATISTICS
  void printStatistics ( ofstream & );
#endif

  friend class GCTest;
};

inline bool Egraph::isInitialized( )
{
  return (solver != NULL && theoryInitialized);
}

inline void Egraph::initDupMap1( )
{
  assert( !active_dup_map1 );
  active_dup_map1 = true;
  dup_map1.growTo( enode_store.id_to_enode.size( ), ERef_Nil );
  dup_set1.growTo( enode_store.id_to_enode.size( ), dup_map_count1 );
  dup_map_count1 ++;
}

inline void Egraph::initDupMap2( )
{
  assert( !active_dup_map2 );
  active_dup_map2 = true;
  dup_map2.growTo( enode_store.id_to_enode.size( ), ERef_Nil );
  dup_set2.growTo( enode_store.id_to_enode.size( ), dup_map_count2 );
  dup_map_count2 ++;
}

inline void Egraph::storeDupMap1( ERef k, ERef e )
{
  assert(  active_dup_map1 );
  dup_map1.growTo( enode_store.id_to_enode.size( ), ERef_Nil ); // Should this be ERef_Undef instead?
  dup_set1.growTo( enode_store.id_to_enode.size( ), dup_map_count1 - 1 );
  Enode& en_k = enode_store[k];
  assert( en_k.getId() < (enodeid_t)dup_set1.size_( ) );
  dup_set1[ en_k.getId() ] = dup_map_count1;
  dup_map1[ en_k.getId( ) ] = e;
}

inline void Egraph::storeDupMap2( ERef k, ERef e )
{
  assert(  active_dup_map2 );
  dup_map2.growTo( enode_store.id_to_enode.size( ), ERef_Undef );
  dup_set2.growTo( enode_store.id_to_enode.size( ), dup_map_count2 - 1 );
  Enode& en_k = enode_store[k];
  assert( en_k.getId( ) < (enodeid_t)dup_set2.size_( ) );
  dup_set2[ en_k.getId( ) ] = dup_map_count2;
  dup_map2[ en_k.getId( ) ] = e;
}

inline ERef Egraph::valDupMap1( ERef k )
{
  assert(  active_dup_map1 );
  dup_map1.growTo( enode_store.id_to_enode.size( ), ERef_Undef );
  dup_set1.growTo( enode_store.id_to_enode.size( ), dup_map_count1 - 1 );
  Enode& en_k = enode_store[k];
  assert( en_k.getId( ) < (enodeid_t)dup_set1.size_( ) );
  if ( dup_set1[ en_k.getId( ) ] == dup_map_count1 )
    return dup_map1[ en_k.getId( ) ];
  return ERef_Undef;
}

inline ERef Egraph::valDupMap2( ERef k )
{
  assert(  active_dup_map2 );
  dup_map2.growTo( enode_store.id_to_enode.size( ), ERef_Undef );
  dup_set2.growTo( enode_store.id_to_enode.size( ), dup_map_count2 - 1 );
  Enode& en_k = enode_store[k];
  assert( en_k.getId( ) < (enodeid_t)dup_set2.size_( ) );
  if ( dup_set2[ en_k.getId( ) ] == dup_map_count2 )
    return dup_map2[ en_k.getId( ) ];
  return ERef_Undef;
}

inline void Egraph::doneDupMap1( )
{
  assert(  active_dup_map1 );
  active_dup_map1 = false;
}

inline void Egraph::doneDupMap2( )
{
  assert(  active_dup_map2 );
  active_dup_map2 = false;
}

#endif
