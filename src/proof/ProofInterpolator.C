/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>
      , Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2008 - 2012 Roberto Bruttomesso

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

#include "ProofGraph.h"

#ifdef PRODUCE_PROOF

//#define INTVERB
//#define MEMVERB

// Input: empty vector, flag for using symmetric or McMillan's system
// Output: sequence of interpolants
void ProofGraph::produceSequenceInterpolants( vector< Enode * > & sequence_of_interpolants )
{
#ifdef MEMVERB
  {
    uint64_t mem_used = memUsed();
    reportf( "# Memory used before generating interpolants: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
  }
#endif
  assert( sequence_of_interpolants.size( ) == 0 );

  // Clause and partial interpolant
  ProofNode * n;
  Enode * partial_interp;

  // Vector for topological ordering
  vector< clauseid_t > DFSv;
  // Compute topological sorting of graph
  topolSortingVec( DFSv );
  size_t proof_size = DFSv.size();

#ifdef MEMVERB
  cout << "Proof size: " << proof_size << endl;
#endif

  //Determine number of partitions
  unsigned num_partitions = egraph.getNofPartitions( );
  //Interpolant partition masks
  ipartitions_t A_mask = 0;
  ipartitions_t B_mask = 0;

#ifdef MEMVERB
  {
    uint64_t mem_used = memUsed();
    reportf( "# Memory used after topol ordering generating interpolants: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 ); 
  }
#endif

  // Compute sequence of interpolants (m with m partitions)
  for( unsigned curr_interp = 0; curr_interp < num_partitions + 1; curr_interp ++ )
  {
#ifdef MEVERB
    size_t sbefore = egraph.size();
#endif

    // Update current interpolant partition mask
    // Set i_th bit to 1 (starting from bit 1, bit 0 is untouched)
    if( curr_interp != 0 ) 
    {
      // A_mask |= SETBIT( curr_interp );
      setbit( A_mask, curr_interp );
    }
    // Determine mask corresponding to B
    B_mask = ~A_mask;
    // Reset bit 0 to 0
    clrbit( B_mask, 0 );

    // Traverse proof and compute current interpolant
    for( size_t i = 0 ; i < proof_size ; i++ )
    {
      n = graph[ DFSv[ i ] ];

      // Generate partial interpolant for clause i
      partial_interp = setPartialInterp( n, curr_interp, A_mask, B_mask );
#ifdef INTVERB
      cout << "Partial interpolant: " << partial_interp << endl << endl;
#endif
    }
#ifdef INTVERB
    cout << "*****************************************" << endl << endl;
#endif

    // Last clause visited is the empty clause with total interpolant
    sequence_of_interpolants.push_back( partial_interp );

#ifdef MEMVERB
    {
      uint64_t mem_used = memUsed();
      reportf( "# Memory used after generating %d interpolants: %.3f MB\n", curr_interp,  mem_used == 0 ? 0 : mem_used / 1048576.0 );
      //std::cout << "Size of interpolant " << curr_interp << ": " << s1 << std::endl;
      //int s1 = getComplexityInterpolantIterative(partial_interp, true);
      cout << "New enodes: " << (egraph.size() - sbefore) << endl;
    }
#endif

    if ( printProofDotty( ) == 1 )
    {
      char buf[ 32 ];
      sprintf( buf, "proof_interp_%d.dot", curr_interp ); 
      ofstream dotty( buf );
      printProofAsDotty( dotty, false );
    }
  }
}

//Input: vectors of partition ids, empty output vector
//Output: sequence of the chosen interpolants filled in the given vector
void ProofGraph::produceChosenInterpolants(const vector<vector<int> > &partitions,
                                           vector<Enode*> &interpolants)
{
  assert(interpolants.size( ) == 0 );

  // Clause and partial interpolant
  ProofNode * n;
  Enode * partial_interp;

  // Vector for topological ordering
  vector< clauseid_t > DFSv;
  // Compute topological sorting of graph
  topolSortingVec( DFSv );
  size_t proof_size = DFSv.size();

  // Interpolant partition masks
  ipartitions_t A_mask = 0;
  ipartitions_t B_mask = 0;

  // Compute sequence of interpolants (m with m partitions)
  for( unsigned curr_interp = 0; curr_interp < partitions.size(); curr_interp ++ )
  {
    const vector<int>& partition = partitions[curr_interp];

    A_mask = 0;
    for (unsigned i = 0; i < partition.size(); ++i) {
      // Set partitions[i] bit to 1 (starting from bit 1, bit 0 is untouched)
      setbit( A_mask, partition[i]+1);
    }
    //Determine mask corresponding to B
    B_mask = ~A_mask;
    //Reset bit 0 to 0
    clrbit( B_mask, 0 );

    // Traverse proof and compute current interpolant
    for( size_t i = 0 ; i < proof_size ; i++ )
    {
      n = graph[ DFSv[ i ] ];

      // Generate partial interpolant for clause i
      partial_interp = setPartialInterp( n, curr_interp, A_mask, B_mask );
#ifdef INTVERB
      cout << "Partial interpolant: " << partial_interp << endl << endl;
#endif
    }
#ifdef INTVERB
    cout << "*****************************************" << endl << endl;
#endif

    // Last clause visited is the empty clause with total interpolant
    interpolants.push_back( partial_interp );

    if ( printProofDotty( ) == 1 )
    {
      char buf[ 32 ];
      sprintf( buf, "proof_interp_%d.dot", curr_interp ); 
      ofstream dotty( buf );
      printProofAsDotty( dotty, false );
    }
  }
}

// Input: flag for using symmetric or McMillan's system
// Output: interpolant obtained splitting in half formula
Enode * ProofGraph::produceMiddleInterpolant( )
{
  // Clause and partial interpolant
  ProofNode * n;
  Enode * partial_interp = NULL;

  // Vector for topological ordering
  vector< clauseid_t > DFSv;
  // Compute topological sorting of graph
  topolSortingVec( DFSv );
  const size_t proof_size = DFSv.size( );

  // Determine number of partitions
  unsigned num_partitions = egraph.getNofPartitions( );
  // Interpolant partition masks
  ipartitions_t A_mask = 0;
  ipartitions_t B_mask = 0;

  // Split approximately in half
  unsigned curr_interp = num_partitions/2;

  //Update current interpolant partition mask
  //Set i_th bit to 1 (starting from bit 1, bit 0 is untouched)
  if( curr_interp != 0 ) 
  {
    // A_mask |= SETBIT( curr_interp );
    setbit( A_mask, curr_interp );
  }
  // Determine mask corresponding to B
  B_mask = ~A_mask;
  // Reset bit 0 to 0
  // FIXME: don't understand this ...
  // B_mask = B_mask & (~((ipartitions_t)SETBIT(0)));
  clrbit( B_mask, 0 );

  //cout << "Nodes " << proof_size << endl;

  // Traverse proof and compute current interpolant
  for( size_t i = 0 ; i < proof_size ; i++ )
  {
    n = graph[ DFSv[ i ] ];
    // Generate partial interpolant for clause i
    partial_interp = setPartialInterp( n, curr_interp, A_mask, B_mask );
#ifdef INTVERB
    cout << "Partial interpolant: " << partial_interp << endl << endl;
#endif
  }
#ifdef INTVERB
  cout << "*****************************************" << endl << endl;
#endif
  return partial_interp;
}

// Input: an interpolant, a boolean
// Output: complexity of interpolant (2 ways depending on the flag)
// Improved iterative implementation using topological visit of enode
int ProofGraph::getComplexityInterpolantIterative(Enode * int_e, bool flag)
{
  assert( int_e );
  assert( int_e->hasSortBool( ) );

  vector< Enode * > DFS_enode;
  topolSortingEnode( DFS_enode, int_e );

  map< Enode *, int > complexity_map;
  Enode * curr_enode;

#ifdef MEMVERB
  cout << "Itp size: " << DFS_enode.size() << endl;
  unsigned long mem = 0;
#endif

  for( size_t i = 0; i < DFS_enode.size( ) ; i++ )
  {
    curr_enode= DFS_enode[i];
    assert(curr_enode!=NULL);

#ifdef MEMVERB
    mem += curr_enode->sizeInMem();
#endif

    // Case atom
    if( curr_enode->isAtom( ) )
    {
      // Complexity of atom is 0
      complexity_map.insert( pair< Enode*, int >( curr_enode, 0 ) );
    }
    // Case boolean connective: and, or not, iff, xor, implies
    else if( curr_enode->isBooleanOperator() )
    {
      Enode * args = curr_enode->getCdr();
      assert( args->isList( ) );

      int comp_curr=0;
      int num_args=0;
      // Scan arguments of connective
      for ( Enode * alist = args ; !alist->isEnil( ) ; alist = alist->getCdr( ) )
      {
        Enode * e = alist->getCar( );
        assert( e->hasSortBool( ) );
        // Calculate complexity
        comp_curr += complexity_map.find(e)->second;
        num_args++;
      }
      if( flag )
      {
        // Complexity of connective is sum of complexities of arguments plus one
        complexity_map.insert(pair<Enode*,int>(curr_enode,comp_curr + 1));
      }
      else
      {
        // Complexity of connective is sum of complexities of arguments plus number of arguments
        complexity_map.insert(pair<Enode*,int>(curr_enode,comp_curr + num_args));
      }
    }
  }
#ifdef MEMVERB
  cout << "Memory occupied by Itp: " << (mem / 1024) << endl;
#endif
  return complexity_map.find(int_e)->second;
}

// Input: an interpolant
// Output: the set of predicates contained in the interpolant
// Better iterative version
// FIXME: Returning a set is a bad idea, turn it into an input parameter
set< Enode * > ProofGraph::getPredicatesSetFromInterpolantIterative(Enode * int_e)
{
  assert( int_e );
  assert( int_e->hasSortBool( ) );

  vector< Enode * > DFS_enode;
  topolSortingEnode( DFS_enode, int_e );

  map< Enode *, set< Enode * > > predicate_map;
  set< Enode * >::iterator it;
  Enode * curr_enode;

  for( size_t i = 0 ; i < DFS_enode.size( ) ; i++ )
  {
    curr_enode = DFS_enode[i];
    assert( curr_enode );

    set< Enode * > pred_set_curr;

    // Case atom
    if( curr_enode->isAtom() )
    {
      pred_set_curr.insert(curr_enode);
      predicate_map.insert(pair< Enode*,set<Enode*> >(curr_enode,pred_set_curr));
    }
    // Case boolean connective: and, or not, iff, xor, implies
    else if( curr_enode->isBooleanOperator() )
    {
      Enode * args = curr_enode->getCdr();
      assert( args->isList( ) );

      // Scan arguments of connective
      for ( Enode * alist = args ; !alist->isEnil( ) ; alist = alist->getCdr( ) )
      {
        Enode * e = alist->getCar( );
        assert( e->hasSortBool( ) );
        // Addalculate predicates
        set<Enode*> sub_pred_set = predicate_map.find(e)->second;
        for(it = sub_pred_set.begin(); it!=sub_pred_set.end(); it++ )
          pred_set_curr.insert((*it));
      }
      // Complexity of connective is sum of complexities of arguments plus one
      predicate_map.insert(pair< Enode*,set<Enode*> >(curr_enode,pred_set_curr));
    }
  }
  return predicate_map.find(int_e)->second;
}

// Input: an empty vector, an enode representing a boolean formula
// Output: a topological sorting of the enode subexpressions
void ProofGraph::topolSortingEnode(vector<Enode*>& DFS, Enode* int_e)
{
  assert( int_e!=NULL );
  assert( int_e->hasSortBool() );
  assert( DFS.empty() );

  vector<Enode*>q;
  Enode* e_curr;
  DFS.clear();
  set<Enode*> visited;
  bool all_visited;

  q.push_back(int_e);
  do
  {
    e_curr=q.back();
    assert(e_curr!=NULL);
    //Node not visited yet
    if(visited.find(e_curr) == visited.end())
    {
      all_visited = false;
      // Atomic boolean expression
      if(e_curr->isAtom())
      {
        all_visited = true;
      }
      // Non atomic boolean expression
      else if( e_curr->isBooleanOperator() )
      {
        Enode * args = e_curr->getCdr();
        assert( args->isList( ) );

        all_visited = true;
        // Scan arguments of connective
        for ( Enode * alist = args ; !alist->isEnil( ) ; alist = alist->getCdr( ) )
        {
          Enode * sub_e = alist->getCar( );
          assert( sub_e->hasSortBool( ) );

          if(visited.find(sub_e) == visited.end())
          {
            q.push_back(sub_e);
            all_visited=false;
          }
        }
      }
      if(all_visited)
      {
        visited.insert(e_curr);
        q.pop_back();
        DFS.push_back(e_curr);
      }
    }
    else
      q.pop_back();
  }
  while(!q.empty());
}

// Input: clause, current interpolant partition masks 
// for A and B, flag for using symmetric or McMillan's system
// Output: partial interpolant for the clause
Enode * ProofGraph::setPartialInterp( ProofNode * n
                                      , int curr_interp
                                      , const ipartitions_t & A_mask
                                      , const ipartitions_t & B_mask )
{
  assert( n );

  // Partial interpolants
  Enode * partial_interp = NULL;

#ifdef INTVERB
  cout << "Clause " ; printClause(n);
  cout << "of type " << n->type << endl;
#endif
  // Node is leaf
  if( n->isLeaf() )
  {
    // Theory lemma
    if( n->getType() == CLALEMMA )
    {
      // NOTE checking whether lemmata are met during interpolant generation.
      // should not be the case for propositional logic proofs
      assert(false);
      // Retrieve partial interpolant for current division into A,B
      partial_interp = getPartialInterp( n, curr_interp );
      assert( partial_interp );
    }
    // Original clause
    else if( n->getType() == CLAORIG )
    {
      // Compute interpolant
      // McMillan's system
      if( usingMcMillanInterpolation( ) )
      {
        partial_interp = setInterpMcMillanLeaf( n, curr_interp, A_mask, B_mask );
      }
      // Symmetric system
      else if( usingPudlakInterpolation( ) )
      {
        partial_interp = setInterpPudlakLeaf( n, curr_interp, A_mask, B_mask );
      }
      // McMillan's prime system
      else if( usingMcMillanPrimeInterpolation( ) )
      {
        partial_interp = setInterpMcMillanPrimeLeaf( n, curr_interp, A_mask, B_mask );
      }
      else 
      {
        opensmt_error( "This line should be unreachable" );
      }
      n->setPartialInterpolant(partial_interp);
    }
    else if ( n->getType() == CLAMAGENTA && n->getPartialInterpolant() == NULL )
    {
      opensmt_error( "This line should be unreachable" );
    }
  }
  // Node is derived
  else
  {
    // Compute interpolant
    // McMillan's system
    if( usingMcMillanInterpolation( ) )
    {
      partial_interp = setInterpMcMillanInner( n, curr_interp, A_mask, B_mask );
    }
    // Symmetric system
    else if( usingPudlakInterpolation( ) )
    {
      partial_interp = setInterpPudlakInner( n, curr_interp, A_mask, B_mask );
    }
    // McMillan's prime system
    else if( usingMcMillanPrimeInterpolation( ) )
    {
      partial_interp = setInterpMcMillanPrimeInner( n, curr_interp, A_mask, B_mask );
    }
    else
    {
      opensmt_error( "This line should be unreachable" );
    }
    n->setPartialInterpolant( partial_interp );
  }
  // Check partial_interp has been computed 
  assert( partial_interp );
  return partial_interp;
}

// Input: leaf clause, current interpolant partition masks for A and B
// Output: McMillan partial interpolant for the clause
Enode * ProofGraph::setInterpMcMillanLeaf( ProofNode * n
                                           , int curr_interp
                                           , const ipartitions_t & A_mask
                                           , const ipartitions_t & B_mask )
{
  // Determine clause color
  icolor_t clause_color = getClauseColor( n, A_mask, B_mask );
  // Original leaves can be only A or B colored
  assert( clause_color == I_A || clause_color == I_B );

  Enode * partial_interp = NULL;

  //Leaf belongs to A -> interpolant = leaf clause restricted to B
  if( clause_color == I_A )
  {
    //Compute clause restricted to B
    vector< Lit > restricted_clause;
    restrictClauseToColor( n, A_mask, B_mask, restricted_clause, I_AB );
    size_t clause_size = restricted_clause.size( );

    //Create enode for the restricted clause
    if( clause_size == 0 )
      //Partial interpolant is false in case of empty clause left
      partial_interp = egraph.mkFalse( );
    else
    {
      //Initialize with first literal
      partial_interp = thandler->varToEnode(var(restricted_clause[0]));
      //Check polarity literal
      if(sign(restricted_clause[0])) partial_interp = egraph.mkNot(egraph.cons(partial_interp));

      Enode * lit;
      for(size_t i=1;i<clause_size;i++)
      {
        lit = thandler->varToEnode(var(restricted_clause[i]));
        //Check polarity literal
        if(sign(restricted_clause[i])) lit = egraph.mkNot(egraph.cons(lit));
        //Build adding literals progressively
        partial_interp = egraph.mkOr(egraph.cons(partial_interp, egraph.cons(lit)));
      }
    }
  }
  //Leaf belongs to B -> interpolant = true
  else if( clause_color == I_B )
    partial_interp = egraph.mkTrue( );
  else
    opensmt_error( "this line should be unreachable" );

  return partial_interp;
}

//Input: non leaf clause, current interpolant partition masks for A and B
//Output: McMillan partial interpolant for the clause
Enode * ProofGraph::setInterpMcMillanInner( ProofNode * n
                                            , int curr_interp
                                            , const ipartitions_t & A_mask
                                            , const ipartitions_t & B_mask
)
{
  //Get antecedents partial interpolants
  Enode* partial_interp_ant1 = NULL;
  Enode* partial_interp_ant2 = NULL;
  partial_interp_ant1 = getPartialInterp( n->getAnt1(), curr_interp );
  partial_interp_ant2 = getPartialInterp( n->getAnt2(), curr_interp );
  assert( partial_interp_ant1 );
  assert( partial_interp_ant2 );

  Enode * partial_interp = NULL;

  // Determine color pivot
  icolor_t pivot_color = getVarColor( n->getPivot(), A_mask, B_mask );

  // Pivot colored A -> interpolant = interpolant of ant1 OR interpolant of ant2
  if( pivot_color == I_A )
    partial_interp = egraph.mkOr( egraph.cons( partial_interp_ant1
                                               , egraph.cons( partial_interp_ant2 ) ) );
  // Pivot colored B or AB -> interpolant = interpolant of ant1 AND interpolant of ant2
  else if( pivot_color == I_B 
      || pivot_color == I_AB )
    partial_interp = egraph.mkAnd( egraph.cons( partial_interp_ant1
                                                , egraph.cons( partial_interp_ant2 ) ) );

  return partial_interp;
}

// Input: leaf clause, current interpolant partition masks for A and B
// Output: McMillan prime partial interpolant for the clause
Enode * ProofGraph::setInterpMcMillanPrimeLeaf( ProofNode * n
                                                , int curr_interp
                                                , const ipartitions_t & A_mask
                                                , const ipartitions_t & B_mask )
{
  // Determine clause color
  icolor_t clause_color = getClauseColor( n, A_mask, B_mask );
  // Original leaves can be only A or B colored
  assert( clause_color == I_A || clause_color == I_B );

  Enode * partial_interp = NULL;
  assert(n->getClauseSize() != 0);

  // Leaf belongs to B -> interpolant = negation of leaf clause restricted to A
  if( clause_color == I_B )
  {
    //Compute clause restricted to A
    vector< Lit > restricted_clause;
    restrictClauseToColor( n, A_mask, B_mask, restricted_clause, I_AB );
    const size_t clause_size = restricted_clause.size( );

    // Create enode for the restricted clause
    if( clause_size == 0 )
      // Partial interpolant is true (negation of false) in case of empty clause left
      partial_interp = egraph.mkTrue( );
    else
    {
      // Remember that we are negating the restricted clause!
      // Literals change polarity and we build an and of literals
      // Initialize with first literal
      partial_interp = thandler->varToEnode( var( restricted_clause[0] ) );
      // Check polarity literal
      if( !sign( restricted_clause[0] ) ) 
        partial_interp = egraph.mkNot( egraph.cons( partial_interp ) );

      Enode * lit = NULL;
      for( size_t i = 1 ; i < clause_size ; i++ )
      {
        lit = thandler->varToEnode( var( restricted_clause[i] ) );
        // Check polarity literal
        if( !sign( restricted_clause[i] ) )
          lit = egraph.mkNot( egraph.cons( lit ) );
        // Build adding literals progressively
        partial_interp = egraph.mkAnd( egraph.cons( partial_interp, egraph.cons( lit ) ) );
      }
    }
  }
  //Leaf belongs to A -> interpolant = false
  else if( clause_color == I_A )
    partial_interp = egraph.mkFalse( );
  else
    opensmt_error( "this line should not be reachable" );

  return partial_interp;
}

// Input: non leaf clause, current interpolant partition masks for A and B
// Output: McMillan prime partial interpolant for the clause
Enode* ProofGraph::setInterpMcMillanPrimeInner( ProofNode * n
                                                , int curr_interp
                                                , const ipartitions_t & A_mask
                                                , const ipartitions_t & B_mask )
{
  // Get antecedents partial interpolants
  Enode * partial_interp_ant1 = NULL;
  Enode * partial_interp_ant2 = NULL;
  partial_interp_ant1 = getPartialInterp( n->getAnt1(), curr_interp );
  partial_interp_ant2 = getPartialInterp( n->getAnt2(), curr_interp );
  assert( partial_interp_ant1 );
  assert( partial_interp_ant2 );

  Enode * partial_interp = NULL;

  // Determine color pivot
  icolor_t pivot_color = getVarColor( n->getPivot(), A_mask, B_mask );

  // Pivot colored A or AB -> interpolant = interpolant of ant1 OR interpolant of ant2
  if( pivot_color == I_A || pivot_color == I_AB )
    partial_interp = egraph.mkOr( egraph.cons( partial_interp_ant1
                                               , egraph.cons( partial_interp_ant2 ) ) );
  // Pivot colored B -> interpolant = interpolant of ant1 AND interpolant of ant2
  else if( pivot_color == I_B )
    partial_interp = egraph.mkAnd( egraph.cons( partial_interp_ant1 
                                                , egraph.cons( partial_interp_ant2 ) ) );

  return partial_interp;
}

// Input: leaf clause, current interpolant partition masks for A and B
// Output: Pudlak partial interpolant for the clause
Enode * ProofGraph::setInterpPudlakLeaf( ProofNode * n
                                         , int curr_interp
                                         , const ipartitions_t & A_mask
                                         , const ipartitions_t & B_mask )
{
  // Determine clause color
  icolor_t clause_color = getClauseColor( n, A_mask, B_mask );
  // Original leaves can be only A or B colored
  assert( clause_color == I_A || clause_color == I_B );

  Enode * partial_interp = NULL;

  //Leaf belongs to A -> interpolant = false
  if( clause_color == I_A )
    partial_interp = egraph.mkFalse( );
  //Leaf belongs to B -> interpolant = true
  else if( clause_color == I_B )
    partial_interp = egraph.mkTrue( );
  else
    opensmt_error( "this line should be unreachable" );

  return partial_interp;
}

// Input: non leaf clause, current interpolant partition masks for A and B
// Output: Pudlak partial interpolant for the clause
Enode * ProofGraph::setInterpPudlakInner( ProofNode * n
                                          , int curr_interp
                                          , const ipartitions_t & A_mask
                                          , const ipartitions_t & B_mask )
{
  // Get antecedents partial interpolants
  Enode * partial_interp_ant1 = NULL;
  Enode * partial_interp_ant2 = NULL;
  partial_interp_ant1 = getPartialInterp( n->ant1, curr_interp );
  partial_interp_ant2 = getPartialInterp( n->ant2, curr_interp );
  assert( partial_interp_ant1 );
  assert( partial_interp_ant2 );

  Enode * partial_interp = NULL;

  // Determine color pivot
  icolor_t pivot_color = getVarColor( n->pivot, A_mask, B_mask );

  // Pivot colored A -> interpolant = interpolant of ant1 AND interpolant of ant2
  if( pivot_color == I_A)
    partial_interp = egraph.mkOr( egraph.cons( partial_interp_ant1
                                               , egraph.cons( partial_interp_ant2 ) ) );
  // Pivot colored B -> interpolant = interpolant of ant1 OR interpolant of ant2
  else if ( pivot_color == I_B )
    partial_interp = egraph.mkAnd( egraph.cons( partial_interp_ant1
                                                , egraph.cons( partial_interp_ant2 ) ) );
  // Pivot colored AB -> interpolant = (pivot OR interpolant of ant1) AND ((NOT pivot) OR interpolant of ant2)
  else if ( pivot_color == I_AB )
  {
    // Find pivot occurrences in ant1 and ant2 and create enodes
    Enode * piv_ = thandler->varToEnode( n->getPivot() );
    // NOTE: if the proof is built correctly, the first antecedents contains the positive occurrence of piv

    Enode * or_1 = egraph.mkOr( egraph.cons( partial_interp_ant1, egraph.cons( piv_ ) ) );
    Enode * or_2 = egraph.mkOr( egraph.cons( partial_interp_ant2, egraph.cons( egraph.mkNot( egraph.cons ( piv_ ) ) ) ) );
    partial_interp = egraph.mkAnd( egraph.cons( or_1, egraph.cons( or_2 ) ) );
  }
  else
    opensmt_error( "this line should not be reachable" );

  return partial_interp;
}

// Input: variable, current interpolant partition masks for A and B
// e.g. 0---010 first partition in A
// Output: returns A-local , B-local or AB-common
icolor_t ProofGraph::getVarColor( Var v
                                  , const ipartitions_t & A_mask
                                  , const ipartitions_t & B_mask )
{
  // Get enode corresponding to variable
  Enode * enode_var = thandler->varToEnode( v );

  //Get partition mask variable
  //e.g. 0---0110 variable in first and second partition
  const ipartitions_t & enode_mask = enode_var->getIPartitions( );

#ifdef INTVERB
  std::cout << "Pivot " << v << " has partition mask " << enode_mask << std::endl;
#endif

  // Check if variable present in A or B
  const bool var_in_A = ( (enode_mask & A_mask) != 0 );
  const bool var_in_B = ( (enode_mask & B_mask) != 0 );
  assert( var_in_A || var_in_B );

  icolor_t var_color;
  // Determine if variable A-local, B-local or AB-common
  if ( var_in_A && !var_in_B ) var_color = I_A;
  else if ( !var_in_A && var_in_B ) var_color = I_B;
  else if (  var_in_A && var_in_B ) var_color = I_AB;
  else
    opensmt_error( "this line should be unreachable" );

#ifdef INTVERB
  cout << "Pivot " << v <<" has color " << var_color << endl;
#endif

  return var_color;
}

// Input: proof node, current interpolant partition masks for A and B
// e.g. 0---010 first partition in A
// Output: returns A or B
icolor_t ProofGraph::getClauseColor( ProofNode * n
                                     , const ipartitions_t & A_mask
                                     , const ipartitions_t & B_mask )
{
  // Get partition mask clause
  // e.g. 0---0110 variable in first and second partition
  const ipartitions_t & clause_mask = n->partition_mask;

  // Check if belongs to A or B
  const bool clause_in_A = ( (clause_mask & A_mask) != 0 );
  const bool clause_in_B = ( (clause_mask & B_mask) != 0 );
  assert( clause_in_A || clause_in_B );

  icolor_t clause_color = I_A;

  // Determine if clause belongs to A or B
  if( clause_in_A && !clause_in_B ) clause_color = I_A;
  else if( !clause_in_A && clause_in_B ) clause_color = I_B;
  else if( clause_in_A && clause_in_B ) clause_color = I_AB;
  else 
    opensmt_error( "this line should be unreachable" );
#ifdef INTVERB
  cout << "Clause has color " << clause_color << endl;
#endif
  return clause_color;
}

// Input: clause in A or clause in B, current interpolant partition masks for A and B
// Output: restricted clause wrt color
void ProofGraph::restrictClauseToColor( ProofNode * n
                                        , const ipartitions_t & A_mask
                                        , const ipartitions_t & B_mask
                                        , vector< Lit > & restricted_clause
                                        , icolor_t color )
{
  icolor_t var_color;
  vector< Lit > & cl = n->getClause();
  const size_t size = cl.size( );
  assert( restricted_clause.size( ) == 0 );

  for( size_t i = 0 ; i < size ; i ++ )
  {
    var_color = getVarColor(var(cl[i]), A_mask, B_mask);
    assert( var_color == I_B || var_color == I_A || var_color == I_AB );
    if( var_color == color ) restricted_clause.push_back( cl[i] );
  }
}


// Input: clause
// Output: partial interpolant for current division into A,B
Enode * ProofGraph::getPartialInterp( ProofNode * n, int curr_interp )
{
  assert( n->partial_interp );

  // Return single partial interpolant in case of non theory lemma
  if( n->type != CLALEMMA ) return n->getPartialInterpolant();

  assert(false);

  Enode * interp = n->partial_interp;

  // First interpolant is always true
  if ( curr_interp == 0 ) return egraph.mkTrue( );

  assert( curr_interp <= static_cast< int >( interp->getArity( ) + 1 ) );

  // Last interpolant is always false
  if ( curr_interp == static_cast< int >( interp->getArity( ) + 1 ) )
    return egraph.mkFalse( );

  // Scan list partial interpolants
  for( int i = 1 ; i < curr_interp ; i++ )
    interp = interp->getCdr( );

  assert( interp->getCar( ) );
  return interp->getCar( );
}

/********** LABELING BASED INTERPOLATION **********/
/**
// Input: leaf clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
Enode * ProofGraph::setInterpLabelingLeaf( ProofNode * n
                                           , int curr_interp
                                           , const ipartitions_t & A_mask
                                           , const ipartitions_t & B_mask )
{
  // Determine clause class
  icolor_t clause_color = getClauseColor( n, A_mask, B_mask );
  // Original leaves can be only of class A or B
  assert( clause_color == I_A || clause_color == I_B );

  Enode * partial_interp = NULL;

  //Leaf belongs to A -> interpolant = leaf clause restricted to B
  if( clause_color == I_A )
  {
    //Compute clause restricted to b
    vector< Lit > restricted_clause;
    restrictClauseToColor( n, A_mask, B_mask, restricted_clause, I_B );
    size_t clause_size = restricted_clause.size( );

    //Create enode for the restricted clause
    if( clause_size == 0 )
      //Partial interpolant is false in case of empty clause left
      partial_interp = egraph.mkFalse( );
    else
    {
      //Initialize with first literal
      partial_interp = thandler->varToEnode(var(restricted_clause[0]));
      //Check polarity literal
      if(sign(restricted_clause[0])) partial_interp = egraph.mkNot(egraph.cons(partial_interp));

      Enode * lit;
      for(size_t i=1;i<clause_size;i++)
      {
        lit = thandler->varToEnode(var(restricted_clause[i]));
        //Check polarity literal
        if(sign(restricted_clause[i])) lit = egraph.mkNot(egraph.cons(lit));
        //Build adding literals progressively
        partial_interp = egraph.mkOr(egraph.cons(partial_interp, egraph.cons(lit)));
      }
    }
  }
  // Leaf belongs to B -> interpolant = negation of leaf clause restricted to A
  else if( clause_color == I_B )
  {
    //Compute clause restricted to a
    vector< Lit > restricted_clause;
    restrictClauseToColor( n, A_mask, B_mask, restricted_clause, I_A );
    const size_t clause_size = restricted_clause.size( );

    // Create enode for the restricted clause
    if( clause_size == 0 )
      // Partial interpolant is true (negation of false) in case of empty clause left
      partial_interp = egraph.mkTrue( );
    else
    {
      // Remember that we are negating the restricted clause!
      // Literals change polarity and we build an and of literals
      // Initialize with first literal
      partial_interp = thandler->varToEnode( var( restricted_clause[0] ) );
      // Check polarity literal
      if( !sign( restricted_clause[0] ) )
        partial_interp = egraph.mkNot( egraph.cons( partial_interp ) );

      Enode * lit = NULL;
      for( size_t i = 1 ; i < clause_size ; i++ )
      {
        lit = thandler->varToEnode( var( restricted_clause[i] ) );
        // Check polarity literal
        if( !sign( restricted_clause[i] ) )
          lit = egraph.mkNot( egraph.cons( lit ) );
        // Build adding literals progressively
        partial_interp = egraph.mkAnd( egraph.cons( partial_interp, egraph.cons( lit ) ) );
      }
    }
  }
  else
    opensmt_error( "this line should be unreachable" );

  return partial_interp;
}

// Input: inner clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
Enode * ProofGraph::setInterpLabelingInner( ProofNode * n
                                            , int curr_interp
                                            , const ipartitions_t & A_mask
                                            , const ipartitions_t & B_mask )
{
  // Get antecedents partial interpolants
  Enode * partial_interp_ant1 = NULL;
  Enode * partial_interp_ant2 = NULL;
  partial_interp_ant1 = getPartialInterp( n->getAnt1(), curr_interp );
  partial_interp_ant2 = getPartialInterp( n->getAnt2(), curr_interp );
  assert( partial_interp_ant1 );
  assert( partial_interp_ant2 );

  Enode * partial_interp = NULL;

  // Determine color pivot, depending on its color in the two antecedents
  icolor_t pivot_color = getPivotColor( n, A_mask, B_mask );

  // Pivot colored a -> interpolant = interpolant of ant1 AND interpolant of ant2
  if( pivot_color == I_A)
    partial_interp = egraph.mkOr( egraph.cons( partial_interp_ant1, egraph.cons( partial_interp_ant2 ) ) );
  // Pivot colored b -> interpolant = interpolant of ant1 OR interpolant of ant2
  else if ( pivot_color == I_B )
    partial_interp = egraph.mkAnd( egraph.cons( partial_interp_ant1, egraph.cons( partial_interp_ant2 ) ) );
  // Pivot colored ab -> interpolant = (pivot OR interpolant of ant1) AND ((NOT pivot) OR interpolant of ant2)
  else if ( pivot_color == I_AB)
  {
    // Find pivot occurrences in ant1 and ant2 and create enodes
    Var piv = n->getPivot();
    Lit l1, l2;
    Enode * piv_1 = NULL, * piv_2 = NULL;
    size_t size;
    size = n->getAnt1()->getClauseSize();
    for( size_t i = 0 ; i < size ; i ++ )
    {
      l1 = n->getAnt1()->getClause()[ i ];
      if( var( l1 ) == piv )
      {
        piv_1 = thandler->varToEnode( var( l1 ) );
        // Check polarity occurrence
        if( sign( l1 ) ) piv_1 = egraph.mkNot( egraph.cons( piv_1 ) );
        break;
      }
    }
    size = n->getAnt2()->getClauseSize( );
    for( size_t i = 0 ; i < size ; i ++ )
    {
      l2 = n->getAnt2()->getClause()[ i ];
      if( var( l2 ) == piv )
      {
        piv_2 = thandler->varToEnode( var( l2 ) );
        //Check polarity occurrence
        if( sign( l2 ) ) piv_2 = egraph.mkNot( egraph.cons( piv_2 ) );
        break;
      }
    }
    assert( piv_1 );
    assert( piv_2 );

    Enode * or_1 = egraph.mkOr( egraph.cons( partial_interp_ant1, egraph.cons( piv_1 ) ) );
    Enode * or_2 = egraph.mkOr( egraph.cons( partial_interp_ant2, egraph.cons( piv_2 ) ) );
    partial_interp = egraph.mkAnd( egraph.cons( or_1, egraph.cons( or_2 ) ) );
  }
  else
    opensmt_error( "this line should not be reachable" );

  return partial_interp;
}

// Input: node, current interpolant partition masks for A and B
// e.g. 0---010 first partition in A
// node
// Output: returns node pivot color as a, b or ab
// depending on the colors in the node antecedents
//TODO determine color instead of class
icolor_t ProofGraph::getPivotColor( ProofNode* n
                                    , const ipartitions_t & A_mask
                                    , const ipartitions_t & B_mask )
{
  Var v = n->getPivot();
  // Get enode corresponding to variable
  Enode * enode_var = thandler->varToEnode( v );

  //Get partition mask variable
  //e.g. 0---0110 variable in first and second partition
  const ipartitions_t & enode_mask = enode_var->getIPartitions( );

#ifdef INTVERB
  //cout << "Pivot " << v << " has partition mask " << enode_mask << endl;
  //printBits(enode_mask);
#endif

  // Check if variable present in A or B
  const bool var_in_A = ( (enode_mask & A_mask) != 0 );
  const bool var_in_B = ( (enode_mask & B_mask) != 0 );
  assert( var_in_A || var_in_B );

  icolor_t var_class = I_A;

  // Determine if variable A-local, B-local or AB-common
  if ( var_in_A && !var_in_B ) var_class = I_A;
  else if ( !var_in_A && var_in_B ) var_class = I_B;
  else if (  var_in_A && var_in_B ) var_class = I_AB;
  else
    opensmt_error( "this line should be unreachable" );

#ifdef INTVERB
  cout << "Pivot " << v <<" has color " << var_class << endl;
#endif
  return var_class;
}
 */
#endif
