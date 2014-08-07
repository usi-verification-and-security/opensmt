/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>
      , Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT2 -- Copyright (C) 2008 - 2012 Roberto Bruttomesso

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

#ifndef PROOFGRAPH_H
#define PROOFGRAPH_H

//TODO remove
#define PRODUCE_PROOF 1

#ifdef PRODUCE_PROOF

#include "ProofGlobal.h"
#include "Proof.h"
#include "Enode.h"
#include "CoreSMTSolver.h"
#include <deque>
#include <algorithm>
#include <limits>
#include <bitset>

//#define CHECK // For general checking
//#define LABELING // For labeling-based interpolation

// Predetermined max size of visit vectors
#define SIZE_BIT_VECTOR 10000000

// Types of clauses
// NB: CLADERIVED are distinct from CLALEARNED during solving, 
// that are the root of the initial subproofs
enum clause_type 
{ 
  CLAORIG
  , CLALEMMA
  , CLAAXIOM
  , CLALEARNT
  , CLAMAGENTA
  , CLADERIVED
};


//
// Resolution proof graph element
// if not make the private
struct ProofNode
{
  ProofNode  ( ) 
  : ant1               ( NULL )
  , ant2               ( NULL )
  , partial_interp     ( NULL )
  , partition_mask     ( 0 )
  { }

  ~ProofNode ( ) { }

  //
  // Getty methods
  //
  inline clauseid_t            getId                  ( ) const { return id; }
  inline vector< Lit > &       getClause              ( )       { return clause; }
  inline size_t                getClauseSize          ( ) const { return clause.size( ); }
  inline Var                   getPivot               ( ) const { return pivot; }
  inline ProofNode *           getAnt1                ( ) const { return ant1; }
  inline ProofNode *           getAnt2                ( ) const { return ant2; }
  inline clause_type           getType                ( ) const { return type; }
  inline Enode *               getPartialInterpolant  ( ) const { return partial_interp; }
  inline const ipartitions_t & getInterpPartitionMask ( ) const { return partition_mask; }
  //
  // Setty methods
  //
  inline void                  setId                  ( clauseid_t new_id )            { id = new_id; }
  inline void                  setPivot               ( Var new_pivot )                { pivot = new_pivot; }
  inline void                  setAnt1                ( ProofNode * a1 )               { ant1 = a1; }
  inline void                  setAnt2                ( ProofNode * a2 )               { ant2 = a2; }
  inline void                  setType                ( clause_type new_type )         { type = new_type; }
  inline void                  setPartialInterpolant  ( Enode * new_part_interp )      { partial_interp = new_part_interp; }
  inline void                  setInterpPartitionMask ( const ipartitions_t & new_part_mask) { partition_mask = new_part_mask; }
  //
  // Test methods
  //
  inline bool           isLeaf(){ assert((ant1==NULL && ant2==NULL) || (ant1!=NULL && ant2!=NULL)); return (ant1==NULL);}
  //
  // Data
  //
  clauseid_t         id;                 // id
  vector< Lit >      clause;             // Clause
  Var                pivot;              // Non-leaf node pivot
  ProofNode *        ant1;               // Edges to antecedents
  ProofNode *        ant2;               // Edges to antecedents 
  clause_type        type;
  Enode *            partial_interp;     // Stores partial interpolant
  ipartitions_t      partition_mask;     // Stores mask
#ifdef LABELING
  vector< icolor_t > labeling;           // Literals labeling
#endif
};

class CoreSMTSolver;
class Proof;

class ProofGraph
{
public:

  ProofGraph ( SMTConfig &     c
               , CoreSMTSolver & s
               , THandler *      th
               , Egraph &        e
               , Proof &         t
               , set< int > &    a
               , int             f
               , clauseid_t      g = clause_id_null
               , int             n = -1 )
  : config   ( c )
  , solver   ( s )
  , thandler ( th )
  , egraph   ( e )
  {
    buildProofGraph( t, a, f, g, n );
    if ( useRandomSeed( ) )
    {
      if ( verbose( ) )
      {
        cout << "# Using random transformation seed" << endl;
      }
      // Initialize random seed
      srand ( time( NULL ) );
    }
    else
    {
      if ( verbose( ) )
      {
        cout << "# Using default transformation seed" << endl;
      }
      // Initialize random seed
      srand ( 1 );
    }
  }

  ~ProofGraph ( );

  void           handleProof		       ( );
  void           handleProofInter	       ( );
  void           initializeLightVarSet         ( set< Var > & );
  void           produceSequenceInterpolants   ( vector< Enode * > & );
  void           produceChosenInterpolants     ( const vector<vector<int> > &,vector<Enode*> &);
  Enode *        produceMiddleInterpolant      ( );

  void           printProofAsDotty             ( ostream &, bool );

  inline int     verbose                       ( ) const { return config.verbosity; }
  inline int     produceInterpolants           ( ) const { return config.produce_inter; }
  inline int     printProofSMT                 ( ) const { return config.print_proofs_smtlib2; }
  inline int     printProofDotty               ( ) const { return config.print_proofs_dotty; }
  inline int     numABMixedPredicates          ( ) { return light_vars.size(); }
  inline size_t  graphSize                     ( ) const { return graph.size( ); }
  inline int     useRandomSeed                 ( ) const { return config.proof_random_seed; }

  void           printBits                     ( const ipartitions_t & ) const;
  //
  // Build et al.
  //
  void           buildProofGraph               ( Proof &, set< int > &, int, clauseid_t, int );
  int            cleanProofGraph               ( );                        // Removes proof leftovers
  void           removeNode                    ( clauseid_t );             // Turn into node destructor (?) FIXME
  //
  // Check et al.
  //
  void           checkClause                        ( clauseid_t );
  void           checkProof                         ( );
  //
  // Auxiliary
  //
  bool           mergeClauses          ( vector< Lit > &, vector< Lit > &, vector< Lit > &, Var );
  inline bool    litLess               ( Lit & l1, Lit & l2 ) { return var(l1) <= var(l2); }
  inline bool    litEq                 ( Lit & l1, Lit & l2 ) { return (var(l1) == var(l2) && sign(l1) == sign(l2)); }
  void           getGraphInfo          ( );
  void           topolSortingVec       ( vector< clauseid_t > & );
  string         printClauseType       ( clause_type );
  void           printProofNode        ( clauseid_t );
  void           printClause           ( ProofNode * );
  void           printClause           ( ProofNode *, ostream & );
  void           printSMTClause        ( ProofNode *, ostream & );
  inline ProofNode* getNode			   ( clauseid_t id ) { assert( id>=0 ); return graph[ id ]; }
  //
  // Interpolation
  //
  Enode *        setPartialInterp                         ( ProofNode *, int, const ipartitions_t &, const ipartitions_t & );
  Enode *        getPartialInterp                         ( ProofNode *, int );
  Enode *        setInterpPudlakLeaf                      ( ProofNode *, int, const ipartitions_t &, const ipartitions_t & );
  Enode *        setInterpPudlakInner                   ( ProofNode *, int, const ipartitions_t &, const ipartitions_t & );
  Enode *        setInterpMcMillanInner                 ( ProofNode *, int, const ipartitions_t &, const ipartitions_t & );
  Enode *        setInterpMcMillanLeaf                    ( ProofNode *, int, const ipartitions_t &, const ipartitions_t & );
  Enode *        setInterpMcMillanPrimeLeaf               ( ProofNode *, int, const ipartitions_t &, const ipartitions_t & );
  Enode *        setInterpMcMillanPrimeInner            ( ProofNode *, int, const ipartitions_t &, const ipartitions_t & );
  void           restrictClauseToColor                       ( ProofNode *, const ipartitions_t &, const ipartitions_t &, vector< Lit > &, icolor_t );
  icolor_t       getVarColor                              ( Var        , const ipartitions_t &, const ipartitions_t & );
  icolor_t       getClauseColor                           ( ProofNode *, const ipartitions_t &, const ipartitions_t & );
  // FIXME: returning a set ?
  set< Enode * > getPredicatesSetFromInterpolantIterative ( Enode * );
  int            getComplexityInterpolantIterative        ( Enode *, bool );
  void           topolSortingEnode                        ( vector< Enode * > &, Enode * );
  bool           usingMcMillanInterpolation               ( ) { return ( config.proof_set_inter_algo == 0 ); }
  bool           usingPudlakInterpolation                 ( ) { return ( config.proof_set_inter_algo == 1 ); }
  bool           usingMcMillanPrimeInterpolation          ( ) { return ( config.proof_set_inter_algo == 2 ); }

private:

  SMTConfig &           config;
  CoreSMTSolver &       solver;
  THandler *            thandler;
  Egraph &              egraph;

  vector< ProofNode * >          graph;                       // Graph
  double                         building_time;               // Time spent building graph
  std::bitset< SIZE_BIT_VECTOR > visited;                     // Bitsets used for graph visits
  std::bitset< SIZE_BIT_VECTOR > visited2;
  set< Var >                     light_vars;                  // Set of light variables that can be pushed up
  clauseid_t                     root;                        // Proof root

  int num_vars_limit;                                         // Number of variables nominal
  int num_vars_actual;                                        // Number of variables actual

  int    num_nodes;                                           // Info on graph dimension
  int    num_edges;
  int    num_unary;
  int    num_leaves;

  double av_cla_size;                                         // Info on clauses
  double var_cla_size;
  int    max_cla_size;
  int    dim_unsat_core;
};

#endif
#endif
