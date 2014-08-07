/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT2 -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

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
