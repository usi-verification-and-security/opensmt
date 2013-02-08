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
#include "TStore.h"
#include "PtStore.h"
#include "Logic.h"
//#include "SigTab.h"
//#include "SplayTree.h"

#ifdef PRODUCE_PROOF
#include "UFInterpolator.h"
#endif

class Egraph : public CoreTSolver
{
private:
  SStore &      sort_store;
  TStore &      sym_store;
  PtStore&      term_store;
  EnodeStore &  enode_store;
  Logic&        logic;
  ERef          ERef_Nil;
  ELAllocator   forbid_allocator;
public:

  Egraph( SMTConfig & c
        , SStore & s, TStore& syms, PtStore& terms, EnodeStore& e, Logic& l )
      : CoreTSolver        ( 0, "EUF Solver", c )
      , sort_store         ( s )
      , sym_store          ( syms )
      , term_store         ( terms )
      , enode_store        ( e )
      , logic              ( l )
      , ERef_Nil           ( e.get_Nil() )
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
  { }

  ~Egraph( )
  {
    backtrackToStackSize( 0 );
#ifdef STATISTICS
    // TODO added for convenience
    if( tsolvers_stats.size() > 0 )
    {
    	if ( config.produce_stats )
    	    {
    	      config.getStatsOut( ) << "# -------------------------" << endl;
    	      config.getStatsOut( ) << "# STATISTICS FOR EUF SOLVER" << endl;
    	      config.getStatsOut( ) << "# -------------------------" << endl;
    	      tsolvers_stats[ 0 ]->printStatistics( config.getStatsOut( ) );
    	    }
        if ( config.print_stats )
        {
          cerr << "# -------------------------" << endl;
          cerr << "# STATISTICS FOR EUF SOLVER" << endl;
          cerr << "# -------------------------" << endl;
          tsolvers_stats[ 0 ]->printStatistics( cerr );
        }
    	delete tsolvers_stats[ 0 ];
    }
#endif
    //
    // Delete Ordinary Theory Solvers
    //
#ifdef STATISTICS
    assert( tsolvers.size( ) == tsolvers_stats.size( ) );
#endif
      // TODO added for convenience
    for ( unsigned i = 1 ; ( config.produce_stats || config.print_stats ) && i < tsolvers.size_( ) ; i ++ )
    {
#ifdef STATISTICS
        if( config.produce_stats )
        {
              config.getStatsOut( ) << "# -------------------------" << endl;
              config.getStatsOut( ) << "# STATISTICS FOR " << tsolvers[ i ]->getName( ) << endl;
              config.getStatsOut( ) << "# -------------------------" << endl;
              assert( tsolvers_stats[ i ] );
              tsolvers_stats[ i ]->printStatistics( config.getStatsOut( ) );
        }
        if( config.print_stats )
        {
               cerr << "# -------------------------" << endl;
               cerr << "# STATISTICS FOR " << tsolvers[ i ]->getName( ) << endl;
               cerr << "# -------------------------" << endl;
               assert( tsolvers_stats[ i ] );
               tsolvers_stats[ i ]->printStatistics( cerr );
        }
      delete tsolvers_stats[ i ];
#endif
      assert( tsolvers[ i ] );
      delete tsolvers[ i ];
    }
    //
    // Delete enodes
    //
    while ( enode_store.id_to_enode.size() != 0 )
    {
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

  size_t size() const { return enode_store.id_to_enode.size(); };

  //
  // Predefined constants nil, true, false
  //
  ERef ERef_true;
  ERef ERef_false;

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

  inline PTRef indexToDistReas ( unsigned index ) const
  {
    assert( index < index_to_dist.size_( ) );
    return index_to_dist[ index ];
  }


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
  inline void initDup1  ( )        { assert( !active_dup1 ); active_dup1 = true; duplicates1.growTo( enode_store.id_to_enode.size( ), dup_count1 ); dup_count1 ++; }
  inline void storeDup1 ( ERef e ) { assert(  active_dup1 ); assert( enode_store[e].getId() < (enodeid_t)duplicates1.size_() ); duplicates1[ enode_store[e].getId( ) ] = dup_count1; }
  inline bool isDup1    ( ERef e ) { assert(  active_dup1 ); assert( enode_store[e].getId() < (enodeid_t)duplicates1.size_() ); return duplicates1[ enode_store[e].getId( ) ] == dup_count1; }
  inline void doneDup1  ( )        { assert(  active_dup1 ); active_dup1 = false; }
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
  lbool               inform                  ( ERef ) { return l_True; }   // Inform the solver about the existence of a theory atom
  bool                assertLit               ( ERef, bool = false ) {return true; } // Assert a theory literal
  void                pushBacktrackPoint      ( );                          // Push a backtrack point
  void                popBacktrackPoint       ( );                          // Backtrack to last saved point
  ERef                getDeduction            ( );                          // Return an implied node based on the current state
  ERef                getSuggestion           ( );                          // Return a suggested literal based on the current state
  vec<ERef> &         getConflict             ( bool = false );             // Get explanation
  bool                check                   ( bool );		            // Check satisfiability
//  void                initializeCong          ( Enode * );                  // Initialize congruence structures for a node
#ifndef SMTCOMP
//  void                computeModel            ( );
//  void                printModel              ( ostream & );                // Computes and print the model
#endif
//  inline void         setUseGmp               ( ) { use_gmp = true; }
//  inline bool         getUseGmp               ( ) { return use_gmp; }
  void                splitOnDemand           ( vec<ERef> &, int ) { };       // Splitting on demand modulo equality
//  void                splitOnDemand           ( ERef, int );                // Splitting on demand
//  bool                checkDupClause          ( ERef, ERef);                // Check if a clause is duplicate
  void                explain                 ( ERef
                                              , ERef
                                              , vector<ERef> & );           // Exported explain
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
#if MORE_DEDUCTIONS
    , ASSERT_NEQ
#endif
  } oper_t;
  //
  // Handy function to swap two arguments of a list
  //
  inline ERef swapList ( ERef args )
  {
    assert( args != ERef_Undef );
    Enode& en = enode_store[args];
    assert( en.isList() );
    assert( en.getArity() == 2 );
    return enode_store.cons( enode_store[en.getCdr()].getCar(), enode_store.cons(en.getCar(), ERef_Nil) );
  }
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
  vec< int >                  duplicates1;                      // Fast duplicate checking
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
  vec< PTRef >                 index_to_dist;                    // Table distinction index --> proper term
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

  bool    assertLit_      ( ERef ) { return true; }             // Assert a theory literal
  //
  // Asserting literals
  //
public:
  bool    assertEq        ( ERef, ERef, PTRef );                // Asserts an equality
  bool    assertNEq       ( ERef, ERef, PTRef );                // Asserts a negated equality
  bool    assertDist      ( ERef, ERef );                       // Asserts a distinction
private:
  //
  // Backtracking
  //
  void backtrackToStackSize ( size_t );                         // Backtrack to a certain operation
  //
  // Congruence closure main routines
  //
  bool    unmergeable     ( ERef, ERef, unsigned int* );        // Can two nodes be merged ? FIXME Why unsigned int* and not PTRef& ??
  void    merge           ( ERef, ERef );                       // Merge two nodes
  bool    mergeLoop       ( PTRef reason );                     // Merge loop
  void    deduce          ( ERef, ERef);                        // Deduce from merging of two nodes
  void    undoMerge       ( ERef );                             // Undoes a merge
  void    undoDisequality ( ERef );                             // Undoes a disequality
  void    undoDistinction ( ERef );                             // Undoes a distinction
  //
  // Explanation routines and data
  //
  void     expExplain           ( );                            // Main routine for explanation
  void     expExplain           ( ERef, ERef, ERef );           // Enqueue equality and explain
  void     expStoreExplanation  ( ERef, ERef, ERef );           // Store the explanation for the merge
  void     expExplainAlongPath  ( ERef, ERef );                 // Store explanation in explanation
  void     expEnqueueArguments  ( ERef, ERef );                 // Enqueue arguments to be explained
  void     expReRootOn          ( ERef );                       // Reroot the proof tree on x
  void     expUnion             ( ERef, ERef );                 // Union of x and y in the explanation
  ERef     expFind              ( ERef );                       // Find for the eq classes of the explanation
  ERef     expHighestNode       ( ERef );                       // Returns the node of the eq class of x that is closest to the root of the explanation tree
  ERef     expNCA               ( ERef, ERef );                 // Return the nearest common ancestor of x and y
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
  vec< ERef >                 undo_stack_term;                  // Keeps track of terms involved in operations
  vec< oper_t >               undo_stack_oper;                  // Keeps track of operations
  vec< ERef >                 explanation;                      // Stores explanation

#if MORE_DEDUCTIONS
  vec< ERef>                  neq_list;
#endif

  vec< ERef >                 exp_pending;                      // Pending explanations
  vec< ERef >                 exp_undo_stack;                   // Keep track of exp_parent merges
  vec< ERef >                 exp_cleanup;                      // List of nodes to be restored
  int                         time_stamp;                       // Need for finding NCA
  int                         conf_index;                       // Index of theory solver that caused conflict

//  Real                        rescale_factor;                   // Rescale factor for DL
//  long                        rescale_factor_l;                 // Rescale factor for DL
//  bool                        use_gmp;                          // Do we have to use gmp?

  void    initializeCongInc ( ERef );                           // Initialize a node in the congruence at runtime
  void    initializeAndMerge( ERef );                           // Initialize a node in the congruence at runtime
  ERef    uCons             ( ERef, ERef );                     // Undoable cons - To create dynamic terms
  void    undoCons          ( ERef );                           // Undoes a cons

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

  void printEqClass              ( ostream &, ERef );
  void printExplanation          ( ostream & );
  void printExplanationTree      ( ostream &, ERef );
  void printExplanationTreeDotty ( ostream &, ERef );
  void printDistinctionList      ( ostream &, ERef );
  void printCbeStructure         ( );
  void printCbeStructure         ( ostream &, ERef, set< int > & );
  void printParents              ( ostream &, ERef);
#if PEDANTIC_DEBUG
  bool checkParents              ( ERef );
  bool checkInvariants           ( );
  bool checkInvariantFLS         ( );
  bool checkInvariantSTC         ( );
  bool checkExp                  ( );
  bool checkExpTree              ( ERef );
  bool checkExpReachable         ( ERef, ERef );
#endif
  bool checkStaticDynamicTable   ( );

#ifdef STATISTICS
  void printStatistics ( ofstream & );
#endif
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
