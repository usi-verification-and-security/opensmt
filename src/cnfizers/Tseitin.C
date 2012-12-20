/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

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

#include "Cnfizer.h"
#include "Tseitin.h"

//
// Performs the actual cnfization
//
bool Tseitin::cnfize(PTRef formula
#ifdef PRODUCE_PROOF
                    , const ipartitions_t partitions
#endif
                    )
{
#ifdef PRODUCE_PROOF
  assert( config.produce_inter == 0 || partitions != 0 );
#endif

  assert(formula != PTRef_Undef);
  assert(ptstore[formula].symb() != sym_AND);
//  Enode * arg_def = egraph.valDupMap1( formula );
  //
  // Formula was cnfized before ...
  //
//  if ( arg_def != NULL )
//  {
//    vector< Enode * > clause;
//    clause.push_back( arg_def );
#ifdef PRODUCE_PROOF
//    if ( config.produce_inter != 0 )
//      return solver.addSMTClause( clause
//	                        , partitions );
#endif
//    return solver.addSMTClause( clause );
//  }

//  vector< Enode * > unprocessed_enodes;       // Stack for unprocessed enodes
//  unprocessed_enodes.push_back( formula );    // formula needs to be processed
  //
  // Visit the DAG of the formula from the leaves to the root
  //
//  while( !unprocessed_enodes.empty( ) )
//  {
//    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
//    if ( egraph.valDupMap1( enode ) != NULL )
//    {
//      unprocessed_enodes.pop_back( );
//      continue;
//    }

//    bool unprocessed_children = false;
//    Enode * arg_list;
//    for ( arg_list = enode->getCdr( ) ;
//	  arg_list != egraph.enil ;
//	  arg_list = arg_list->getCdr( ) )
//    {
//      Enode * arg = arg_list->getCar( );

//      assert( arg->isTerm( ) );
      //
      // Push only if it is an unprocessed boolean operator
      //
//      if ( enode->isBooleanOperator( )
//	&& egraph.valDupMap1( arg ) == NULL )
//      {
//	unprocessed_enodes.push_back( arg );
//	unprocessed_children = true;
//      }
      //
      // If it is an atom (either boolean or theory) just
      // store it in the cache
      //
//      else if ( arg->isAtom( ) )
//      {
//	egraph.storeDupMap1( arg, arg );
//      }
//    }
    //
    // SKip if unprocessed_children
    //
//    if ( unprocessed_children )
//      continue;

//    unprocessed_enodes.pop_back( );
//    Enode * result = NULL;
    //
    // At this point, every child has been processed
    //
    //
    // Do the actual cnfization, according to the node type
    //
//    char def_name[ 32 ];

//    if ( enode->isLit( ) )
//    {
//      result = enode;
//    }
//    else if ( enode->isNot( ) )
//    {
//      Enode * arg_def = egraph.valDupMap1( enode->get1st( ) );
//      assert( arg_def );
//      result = egraph.mkNot( egraph.cons( arg_def ) ); // Toggle the literal
//    }
//    else
//    {
//      Enode * arg_def = NULL;
//      Enode * new_arg_list = egraph.copyEnodeEtypeListWithCache( enode->getCdr( ) );
      //
      // If the enode is not top-level it needs a definition
      //
//      if ( formula != enode )
//      {
//	sprintf( def_name, CNF_STR, formula->getId( ), enode->getId( ) );
//	egraph.newSymbol( def_name, NULL, sstore.mkBool( ) );
//	arg_def = egraph.mkVar( def_name );
#ifdef PRODUCE_PROOF
//	if ( config.produce_inter != 0 )
//	{
//	  arg_def->setIPartitions( partitions );
//	  egraph.addDefinition( arg_def, enode );
//	}
#endif
//      }
      //
      // Handle boolean operators
      //
//      if ( enode->isAnd( ) )
//	cnfizeAnd( new_arg_list
//		 , arg_def 
//#ifdef PRODUCE_PROOF
//		 , partitions
//#endif	    
//        );
//      else if ( enode->isOr( ) )
//	cnfizeOr( new_arg_list
//	        , arg_def
//#ifdef PRODUCE_PROOF
//	        , partitions
//#endif	    
//        );
//      else if ( enode->isIff( ) )
//	cnfizeIff( new_arg_list
//	         , arg_def
//#ifdef PRODUCE_PROOF
//		 , partitions
//#endif	    
//        );
//      else if ( enode->isXor( ) )
//	cnfizeXor( new_arg_list
//	         , arg_def 
//#ifdef PRODUCE_PROOF
//	         , partitions
//#endif	    
//        );
//      else
//      {
//	opensmt_error2( "operator not handled ", enode->getCar( ) );
//      }

//      if ( arg_def != NULL )
//	result = arg_def;
//    }

//    assert( egraph.valDupMap1( enode ) == NULL );
//    egraph.storeDupMap1( enode, result );
//  }

//  if ( formula->isNot( ) )
//  {
    // Retrieve definition of argument
//    Enode * arg_def = egraph.valDupMap1( formula->get1st( ) );
//    assert( arg_def );
//    vector< Enode * > clause;
//    clause.push_back( toggleLit( arg_def ) );
//#ifdef PRODUCE_PROOF
//    if ( config.produce_inter > 0 )
//      return solver.addSMTClause( clause
//	                        , partitions );
//#endif
//    return solver.addSMTClause( clause );
//  }

  return true;
}

/*
void Tseitin::cnfizeAnd( Enode * list
                       , Enode * arg_def
#ifdef PRODUCE_PROOF
                       , const ipartitions_t partitions
#endif
                       )
{
  assert( list );
  assert( list->isList( ) );
  if ( arg_def == NULL )
  {
    for ( ; list != egraph.enil ; list = list->getCdr( ) )
    {
      Enode * arg = list->getCar( );
      vector< Enode * > little_clause;
      little_clause.push_back( arg );
#ifdef PRODUCE_PROOF
      if ( config.produce_inter > 0 )
	solver.addSMTClause( little_clause, partitions );
      else
#endif
      solver.addSMTClause( little_clause );        // Adds a little clause to the solver
    }
  }
  else
  {
    //
    // ( a_0 & ... & a_{n-1} )
    //
    // <=>
    //
    // aux = ( -aux | a_0 ) & ... & ( -aux | a_{n-1} ) & ( aux & -a_0 & ... & -a_{n-1} )
    //
    vector< Enode * > little_clause;
    vector< Enode * > big_clause;
    little_clause.push_back( toggleLit( arg_def ) );
    big_clause   .push_back( arg_def );
    for ( ; list != egraph.enil ; list = list->getCdr( ) )
    {
      Enode * arg = list->getCar( );
      little_clause.push_back( arg );
      big_clause   .push_back( toggleLit( arg ) );
#ifdef PRODUCE_PROOF
      if ( config.produce_inter > 0 )
	solver.addSMTClause( little_clause, partitions );
      else
#endif
      solver       .addSMTClause( little_clause );        // Adds a little clause to the solver
      little_clause.pop_back( );
    }
#ifdef PRODUCE_PROOF
      if ( config.produce_inter > 0 )
	solver.addSMTClause( big_clause, partitions );
      else
#endif
    solver.addSMTClause( big_clause );                    // Adds a big clause to the solver
  }
}

void Tseitin::cnfizeOr( Enode * list
                      , Enode * arg_def
#ifdef PRODUCE_PROOF
                      , const ipartitions_t partitions
#endif
                      )
{
  assert( list );
  assert( list->isList( ) );
  if ( arg_def == NULL )
  {
    vector< Enode * > big_clause;
    for ( ; list != egraph.enil ; list = list->getCdr( ) )
    {
      Enode * arg = list->getCar( );
      big_clause.push_back( arg );
    }
#ifdef PRODUCE_PROOF
      if ( config.produce_inter > 0 )
	solver.addSMTClause( big_clause, partitions );
      else
#endif
    solver.addSMTClause( big_clause );        
  }
  else
  {
    //
    // ( a_0 | ... | a_{n-1} )
    //
    // <=>
    //
    // aux = ( aux | -a_0 ) & ... & ( aux | -a_{n-1} ) & ( -aux | a_0 | ... | a_{n-1} )
    //
    vector< Enode * > little_clause;
    vector< Enode * > big_clause;
    little_clause.push_back( arg_def );
    big_clause   .push_back( toggleLit( arg_def ) );
    for ( ; list != egraph.enil ; list = list->getCdr( ) )
    {
      Enode * arg = list->getCar( );
      little_clause.push_back( toggleLit( arg ) );
      big_clause   .push_back( arg );
#ifdef PRODUCE_PROOF
      if ( config.produce_inter > 0 )
	solver.addSMTClause( little_clause, partitions );
      else
#endif
      solver       .addSMTClause( little_clause );        // Adds a little clause to the solver
      little_clause.pop_back( );
    }
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( big_clause, partitions );
    else
#endif
    solver.addSMTClause( big_clause );                    // Adds a big clause to the solver
  }
}

void Tseitin::cnfizeXor( Enode * list
                       , Enode * arg_def
#ifdef PRODUCE_PROOF
		       , const ipartitions_t partitions
#endif
                       )
{
  assert( list );
  if ( arg_def == NULL )
  {
    Enode * arg0 = list->getCar();
    Enode * arg1 = list->getCdr( )->getCar();

    vector< Enode * > clause;

    clause.push_back( arg0 );
    clause.push_back( arg1 );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );        

    clause.pop_back( );
    clause.pop_back( );

    clause.push_back( toggleLit( arg0 ) );
    clause.push_back( toggleLit( arg1 ) );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );        
  }
  else
  {
    //
    // ( a_0 xor a_1 )
    //
    // <=>
    //
    // aux = ( -aux | a_0  | a_1 ) & ( -aux | -a_0 | -a_1 ) &
    //       (  aux | -a_0 | a_1 ) & (  aux |  a_0 | -a_1 )
    //
    Enode * arg0 = list->getCar( );
    Enode * arg1 = list->getCdr( )->getCar( );
    vector< Enode *> clause;

    clause.push_back( toggleLit( arg_def ) );

    // First clause
    clause.push_back( arg0 );
    clause.push_back( arg1 );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions ); 
    else
#endif
    solver.addSMTClause( clause ); // Adds a little clause to the solver
    clause.pop_back( );
    clause.pop_back( );

    // Second clause
    clause.push_back( toggleLit( arg0 ) );
    clause.push_back( toggleLit( arg1 ) );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions ); 
    else
#endif
    solver.addSMTClause( clause ); // Adds a little clause to the solver
    clause.pop_back( );
    clause.pop_back( );

    clause.pop_back( );
    clause.push_back( arg_def );

    // Third clause
    clause.push_back( toggleLit( arg0 ) );
    clause.push_back( arg1 );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause ); // Adds a little clause to the solver
    clause.pop_back( );
    clause.pop_back( );

    // Fourth clause
    clause.push_back( arg0 );
    clause.push_back( toggleLit( arg1 ) );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );           // Adds a little clause to the solver
  }
}

void Tseitin::cnfizeIff( Enode * list
                       , Enode * arg_def
#ifdef PRODUCE_PROOF
		       , const ipartitions_t partitions
#endif
                       )
{
  if ( arg_def == NULL )
  {
    Enode * arg0 = list->getCar();
    Enode * arg1 = list->getCdr( )->getCar();

    vector< Enode * > clause;

    clause.push_back( arg0 );
    clause.push_back( toggleLit( arg1 ) );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
	                         
    else
#endif
    solver.addSMTClause( clause );        

    clause.pop_back( );
    clause.pop_back( );

    clause.push_back( toggleLit( arg0 ) );
    clause.push_back( arg1 );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );        
  }
  else
  {
    //
    // ( a_0 <-> a_1 )
    //
    // <=>
    //
    // aux = ( -aux |  a_0 | -a_1 ) & ( -aux | -a_0 |  a_1 ) &
    //	   (  aux |  a_0 |  a_1 ) & (  aux | -a_0 | -a_1 )
    //
    assert( list->getArity( ) == 2 );
    Enode * arg0 = list->getCar( );
    Enode * arg1 = list->getCdr( )->getCar( );
    vector< Enode * > clause;

    clause.push_back( toggleLit( arg_def ) );

    // First clause
    clause.push_back( arg0 );
    clause.push_back( toggleLit( arg1 ) );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );           // Adds a little clause to the solver
    clause.pop_back( );
    clause.pop_back( );

    // Second clause
    clause.push_back( toggleLit( arg0 ) );
    clause.push_back( arg1 );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );           // Adds a little clause to the solver
    clause.pop_back( );
    clause.pop_back( );

    clause.pop_back( );
    clause.push_back( arg_def );

    // Third clause
    clause.push_back( arg0 );
    clause.push_back( arg1 );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );           // Adds a little clause to the solver
    clause.pop_back( );
    clause.pop_back( );

    // Fourth clause
    clause.push_back( toggleLit( arg0 ) );
    clause.push_back( toggleLit( arg1 ) );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );           // Adds a little clause to the solver
  }
}

void Tseitin::cnfizeIfthenelse( Enode * list
                              , Enode * arg_def
#ifdef PRODUCE_PROOF
                              , const ipartitions_t partitions
#endif
                              )
{
  if ( arg_def == NULL )
  {
    Enode * i = list->getCar();
    Enode * t = list->getCdr( )->getCar( );
    Enode * e = list->getCdr( )->getCdr( )->getCar( );

    vector< Enode * > clause;

    clause.push_back( toggleLit( i ) );
    clause.push_back( t );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );        

    clause.pop_back( );
    clause.pop_back( );

    clause.push_back( i );
    clause.push_back( e );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );        
  }
  else
  {
    //  (!a | !i | t) & (!a | i | e) & (a | !i | !t) & (a | i | !e)
    //
    // ( if a_0 then a_1 else a_2 )
    //
    // <=>
    //
    // aux = ( -aux | -a_0 |  a_1 ) &
    //       ( -aux |  a_0 |  a_2 ) &
    //       (  aux | -a_0 | -a_1 ) &
    //       (  aux |  a_0 | -a_2 )
    //
    assert( list->getArity( ) == 3 );
    Enode * arg0 = list->getCar( );
    Enode * arg1 = list->getCdr( )->getCar( );
    Enode * arg2 = list->getCdr( )->getCdr( )->getCar( );
    vector< Enode * > clause;

    clause.push_back( toggleLit( arg_def ) );

    // First clause
    clause.push_back( toggleLit( arg0 ) );
    clause.push_back( arg1 );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );
    clause.pop_back( );
    clause.pop_back( );

    // Second clause
    clause.push_back( arg0 );
    clause.push_back( arg2 );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );
    clause.pop_back( );
    clause.pop_back( );

    clause.pop_back( );
    clause.push_back( arg_def );

    // Third clause
    clause.push_back( toggleLit( arg0 ) );
    clause.push_back( toggleLit( arg1 ) );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );
    clause.pop_back( );
    clause.pop_back( );

    // Fourth clause
    clause.push_back( arg0 );
    clause.push_back( toggleLit( arg2 ) );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );
  }
}
*/

