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

#include "Egraph.h"
#include "SStore.h"
#include "SMTConfig.h"

#ifndef REWRITE_H
#define REWRITE_H

#define REDUCE_TO_EUF  1
#define SPLIT_ON_DEMAND 0

#ifdef PRODUCE_PROOF

#define COLORED_RULES 1

#if COLORED_RULES
#define COL_START( C ) \
{ \
  ipartitions_t color = 0; \
  if ( C == 2 ) color = 31; \
  else if ( C == 4 ) color = 34; \
  else if ( C == 6 ) color = 32; \
  os.flush( ); \
  os << "\033[1" << ";" << color << "m"; \
  os.flush( ); \
} \

#define COL_END \
{ \
  os.flush( ); \
  os << "\033[0m"; \
  os.flush( ); \
}
#else
#define COL_START( C ) { }
#define COL_END { }
#endif

#endif

class RewriteEngine
{
public:

  RewriteEngine( const int           id_ 
               , SMTConfig &         config_ 
	       , Egraph &            egraph_ 
	       , SStore &            sstore_ 
               , vector< Enode * > & explanation_ 
	       , vector< Enode * > & deductions_
#if OUTSPLIT
	       , vector< Enode * > & suggestions_
#endif
		)
    : id              ( id_ )
    , config          ( config_ )
    , egraph          ( egraph_ )
    , sstore          ( sstore_ )
    , explanation     ( explanation_ )
    , deductions      ( deductions_ )
    , status          ( l_Undef )
  { }

  ~RewriteEngine ( )
  {
    backtrackToStackSize( 0 );
  }

  void    check              ( const bool );

  void    addIndexEq         ( Enode * );   // Add Index EQ
  void    addEq              ( Enode * );   // Add eq
  void    addNeq             ( Enode * );   // Add neq

  void    remIndexEq         ( Enode * );  
  void    remEq              ( Enode * );
  void    remNeq             ( Enode * );

  void    pushBacktrackPoint ( );           // Adds backtrack point
  void    popBacktrackPoint  ( );           // Restore backtrack point

  void    printGroundRules   ( );  
  void    printNeqs          ( );

  inline lbool getStatus     ( ) const { return status; }
  inline void  resetStatus   ( )       { status = l_Undef; }

#ifdef PRODUCE_PROOF
  bool    isAlocal           ( Enode * );
  bool    isBlocal           ( Enode * );
  bool    isABcommon         ( Enode * );
  void    addNeqB            ( Enode * );   // Add neq
  void    remNeqB            ( Enode * );
  void    informIdx          ( Enode * );
  Enode * getInterpolant     ( );
#endif

private:

  struct RewriteRule
  {
    RewriteRule( Enode * l
	       , Enode * r
	       , Enode * e
               , vector< RewriteRule * > & r_antec_ 
               , vector< Enode * > & e_antec_ 
	       , bool p = false
	       )
      : lhs          ( l )
      , rhs          ( r )
      , reason       ( e )
      , r_antec      ( r_antec_ )
      , e_antec      ( e_antec_ )
      , enabled      ( true )
#ifdef PRODUCE_PROOF
      , partitions   ( 0 )
      , propagated   ( p )
#endif
    { 
      (void)p;
      assert( checkSelfReference( ) );
#ifdef PRODUCE_PROOF
      setIPartitions( );
#endif
    }

    Enode *                 lhs;        // Head 
    Enode *                 rhs;        // Tail
    Enode *                 reason;     // Reason for rewriting
    vector< RewriteRule * > r_antec;    // Antecedents
    vector< Enode * >       e_antec;    // Neq antecedents
    bool                    enabled;    // Is enabled
#ifdef PRODUCE_PROOF
    ipartitions_t           partitions; // Partition mask
    bool                    propagated;
#endif

    inline friend ostream &  operator<<( ostream & os, RewriteRule * r ) 
    { 
      assert( r ); 
      os << r->lhs; 
#ifdef PRODUCE_PROOF
      COL_START( r->partitions );
#endif
      os << " --> ";
#ifdef PRODUCE_PROOF
      COL_END;
#endif
      os << r->rhs; 
      return os; 
    }

    // Rule must not have itself as antec
    bool checkSelfReference( )
    {
      for ( size_t i = 0 ; i < r_antec.size( ) ; i ++ )
	if ( r_antec[ i ] == this )
	  return false;
      return true;
    }

#ifdef PRODUCE_PROOF
    void setIPartitions( ) 
    { 
      partitions = 0;

      if ( reason )
	partitions = reason->getIPartitions( );

      for ( size_t i = 0 ; i < r_antec.size( ) ; i ++ )
      {
	assert( r_antec[ i ]->partitions != 0 );
	if ( partitions == 0 )
	  partitions = r_antec[ i ]->partitions;
	else
	  partitions &= r_antec[ i ]->partitions;
	assert( partitions != 0 );	
      }

      if ( propagated && partitions == 2 )
	partitions = 4;
      else if ( propagated && partitions == 4 )
	partitions = 2;
    }
#endif
  };

  typedef map< Enode *, RewriteRule * > ground_rules_t;

  void    addIndexRule          ( Enode *, Enode *, Enode *, vector< RewriteRule * > & );

  void    addGroundRule         ( Enode *, Enode *, Enode * );

  void    addGroundRule         ( Enode *                         // lhs
                                , Enode *                         // rhs
                                , Enode *                         // reason
				, ground_rules_t &
                                , vector< RewriteRule * > &       // Add ground rule
                                , vector< Enode * > & );          // Add ground rule

  void    disableGroundRule     ( ground_rules_t &, RewriteRule * );

  Enode * rewrite               ( ground_rules_t &
                                , Enode *
				, vector< RewriteRule * > &
				, vector< Enode * > &
				); // Rewrite input node exhaustively 

  Enode * rewriteGround         ( ground_rules_t &
                                , Enode *
				, vector< RewriteRule * > & 
				, vector< Enode * > &
				);

  Enode * rewriteGeneric        ( Enode *, vector< Enode * > & );

  bool    complete              ( ground_rules_t &
                                , const bool = false );         // Perform completion

  int     postProcessing        ( ground_rules_t &
                                , vector< Enode * > & 
				, vector< Enode * > &
                                , const bool = false );
                                
  void    retrieveIndexes       ( Enode *, vector< Enode * > & );

  bool    lessThan              ( Enode *, Enode * );
  bool    greaterThan           ( Enode *, Enode * );
  int     orient                ( Enode **, Enode ** );
  void    backtrackToStackSize  ( size_t );                            // Restores to a previous size
  void    explain               ( vector< RewriteRule * > & );

  void    applyC1C2             ( ground_rules_t &           // List of ground rules to use
                                , Enode *                    // lhs array variable
                                , Enode *, Enode *           // rhs array store terms
                                , vector< RewriteRule * > &  // r antecedents
                                , vector< Enode * > & );     // e antecedents
       
  void    applyC3               ( ground_rules_t & );

  bool    reduction             ( ground_rules_t & );

  void    failure               ( ground_rules_t &
                                , vector< Enode * > & );

  void    addAndComplete        ( Enode *
                                , Enode *
				, Enode *
				, ground_rules_t & 
				, vector< RewriteRule * > &
				, vector< Enode * > &
				, const bool = false );  // Return true if added

  void    check_                ( ground_rules_t &, vector< Enode * > & );

  void    addBackToDatabase     ( RewriteRule * );                                              // Return true if added
  void    remFromDatabase       ( ground_rules_t &, RewriteRule * );             

  Enode * getRoot               ( Enode * );

  void    printRules            ( ground_rules_t & );

  void    indexExplain          ( Enode *, Enode *, vector< Enode * > & );

  bool    storeEquiv            ( Enode *, Enode * );

  void    deduce                ( );
  //
  // Functions for interpolation go here !
  //
#ifdef PRODUCE_PROOF
  void    replaceInNeqs                ( Enode *, Enode * );
  void    replaceInRules               ( Enode *, Enode * );
  void    replaceIndexInRules          ( ground_rules_t &, Enode *, Enode * );
  bool    unmergable                   ( Enode *, Enode * );
  void    addAndComplete               ( RewriteRule *, ground_rules_t & );
  void    interpolate                  ( Enode *
                                       , vector< RewriteRule * > & );
  void    iCheck                       ( size_t );
  void    addBadSelect                 ( Enode *
                                       , Enode *
			               , Enode *
			               , vector< RewriteRule * > &
			               , vector< Enode * > & );
  void    addBadlyOrientable           ( Enode *
                                       , Enode *
			               , Enode *
			               , vector< RewriteRule * > &
			               , vector< Enode * > & );
  void    assignPartitionsFrom         ( Enode *, Enode * ); 
  void    assignPartitionsFrom         ( Enode *, Enode *, Enode * ); 
  void    assignPartitionsFrom         ( Enode *, Enode *, Enode *, Enode * );
  bool    checkInvariants              ( Enode *, Enode * );
  Enode * getIndexParts                ( Enode * );
  bool    isAlocal                     ( RewriteRule * );
  bool    isBlocal                     ( RewriteRule * );
  bool    isABcommon                   ( RewriteRule * );
  bool    checkInterpolant             ( Enode * );
  void    handleBadlyOrientable        ( const size_t );
  void    setCustomLessThan            ( Enode *, Enode * );
  Enode * freshVarFrom                 ( Enode * );
  bool    areNewIdx                    ( Enode *, Enode * );
  void    accumulateAndFlushExplantion ( );
  void    computeIdxEqClasses          ( );
  Enode * substitute                   ( Enode * );
  void    fixBadlyOrientable           ( );
  void    fixBadSelect                 ( );
  bool    checkCanonizedStore          ( Enode * );
#endif
#if REDUCE_TO_EUF
  void    minimizeExplanation          ( );
#endif
  //
  // Defines the set of operations that can be performed and that should be undone
  //
  typedef enum { 
    ADD_GROUND_RULE          // Adding ground rule
  , ADD_INDEX_RULE           // Adding generic rule
  , DISABLE_RULE             // Disables a rewrite rule
  , ADD_DISABLED_GROUND_RULE // Adds a ground rule already disabled
  , ADD_PROP_RULE            // Propagated rule
#ifdef PRODUCE_PROOF
  , ADD_DEFINE0
  , ADD_GROUND_B_RULE
  , ADD_REPL_GROUND_RULE
  , ADD_REPL_GROUND_B_RULE
  , ADD_BADLY_ORIENTABLE
  , ADD_BAD_SELECT
  , SET_CUSTOM_LT
  , PROPAGATE_A_NEQ
  , PROPAGATE_B_NEQ
  , REPLACED_RULE
  , INDEX_MERGE
#endif
  } oper_t;

  const int                id;
  SMTConfig &              config;
  Egraph &                 egraph;
  SStore &                 sstore;
  vector< Enode * > &      explanation;
  vector< Enode * > &      deductions;
  set< Enode * >           seen_in_expl;
  vector< Enode * >        select_equalities_to_add;
  vector< Enode * >        store_equalities_to_add;

  ground_rules_t           ground_rules;      // List of ground rules    

  vector< oper_t >         undo_stack_oper;   
  vector< RewriteRule * >  undo_stack_term;
  vector< size_t >         backtrack_points;
  set< size_t >            reduced_diffs;

  // Needed for Condition (ii) of tuning
  vector< RewriteRule * >  diff_list;         // List of index rules with diff
  vector< Enode * >        read_list;         // List of read terms seen

  vector< Enode * >        eq_list;           // List of equalities
  vector< Enode * >        neq_list;          // List of negated equalities
  set< Pair( Enode * ) >   neq_set;           // Set of neqs, for eager checks

  map< Enode *, Enode * >  diff_to_index;     // diff(...) = i
  map< Enode *, Enode * >  index_to_diff;     // diff(...) = i

  set< Pair( int ) >       active_rule_set;   // Set of active rules

  lbool                    status;

  // Additional data structures for interpolation
#ifdef PRODUCE_PROOF
  set< RewriteRule * >      bo_to_skip;
  vector< Enode * >         eqs_to_add;
  vector< Enode * >         idx_to_add;
  vector< Enode * >         idx_list;
  ground_rules_t            ground_rules_b;
  vector< Enode * >         neq_list_b;        // List of negated equalities
  set< Pair( Enode * ) >    custom_lt;
  vector< RewriteRule * >   badly_orientable;
  vector< RewriteRule * >   bad_selects;
  vector< Pair( Enode * ) > undo_stack_cust;
  vector< Pair( Enode * ) > undo_stack_repl;
  bool                      turn_A;
  Enode *                   interpolant;
  set< Enode * >            idx_eq_classes_a;
  set< Enode * >            idx_eq_classes_b;
  set< Enode * >            new_indexes;
  map< Enode *, Enode * >   definitions;
  vector< Enode * >         def_stack;
  vector< Enode * >         acc_expl;
  set< RewriteRule * >      internals;
  // map< Enode *, Enode * >   new_indexes_to_A_root;
  // map< Enode *, Enode * >   new_indexes_to_B_root;
  set< Enode * >            ab_common_class;
#endif

#if REDUCE_TO_EUF
  map< Enode *, vector< Enode * > >   eqs_to_antec;
#if SPLIT_ON_DEMAND
  Enode *                             candidate;
  size_t                              nof_idxs;
#endif
#endif
};

#endif
