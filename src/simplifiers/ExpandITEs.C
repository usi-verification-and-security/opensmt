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

#include "ExpandITEs.h"

Enode *
ExpandITEs::doit( Enode * formula )
{
  assert( formula );
  list< Enode * > new_clauses;
  vector< Enode * > unprocessed_enodes;
  egraph.initDupMap1( );

  unprocessed_enodes.push_back( formula );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( ) ;
	  arg_list != egraph.enil ;
	  arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );

      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( egraph.valDupMap1( arg ) == NULL )
      {
	unprocessed_enodes.push_back( arg );
	unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );
    Enode * result = NULL;
    //
    // At this point, every child has been processed
    //
    char def_name[ 32 ];

    if ( enode->isIte( ) )
    {
      //
      // Retrieve arguments
      //
      Enode * i = egraph.valDupMap1( enode->get1st( ) );
      Enode * t = egraph.valDupMap1( enode->get2nd( ) );
      Enode * e = egraph.valDupMap1( enode->get3rd( ) );
      Enode * not_i = egraph.mkNot( egraph.cons( i ) );
      //
      // Generate variable symbol
      //
      sprintf( def_name, ITE_STR, enode->getId( ) );
      Snode * sort = enode->getRetSort( );
      egraph.newSymbol( def_name, NULL, sort );
      //
      // Generate placeholder
      //
      result = egraph.mkVar( def_name );
#ifdef PRODUCE_PROOF
      if ( config.produce_inter != 0 )
	egraph.addDefinition( result, enode );
#endif
      //
      // Generate additional clauses
      //
      Enode * eq_then = egraph.mkEq( egraph.cons( result
	                           , egraph.cons( t ) ) );
      Enode * eq_else = egraph.mkEq( egraph.cons( result
	                           , egraph.cons( e ) ) );
      new_clauses.push_back( egraph.mkOr( egraph.cons( not_i
	                                , egraph.cons( eq_then ) ) ) );
      new_clauses.push_back( egraph.mkOr( egraph.cons( i
	                                , egraph.cons( eq_else ) ) ) );
    }
    else
    {
      result = egraph.copyEnodeEtypeTermWithCache( enode );
    }

    assert( result );
    assert( egraph.valDupMap1( enode ) == NULL );
    egraph.storeDupMap1( enode, result );
  }

  Enode * new_formula = egraph.valDupMap1( formula );
  assert( new_formula );
  egraph.doneDupMap1( );

  new_clauses.push_back( new_formula );

  return egraph.mkAnd( egraph.cons( new_clauses ) );
}
