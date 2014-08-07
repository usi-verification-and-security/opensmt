/*********************************************************************
 Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>
       , Aliaksei Tsitovich  <aliaksei.tsitovich@usi.ch>
       , Edgar Pek           <edgar.pek@usi.ch>

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

#include "DLRescale.h"

void DLRescale::doit( Enode * formula )
{
  if ( formula->isTrue( ) || formula->isFalse( ) )
    return;

#if USE_GMP
  assert( formula );

  int nof_variables = 0;
  mpz_t lcm;
  mpz_init_set_ui( lcm, 1 );

  egraph.initDup1( );

  vector< Enode *> unprocessed_enodes;     // stack for unprocessed enodes
  unprocessed_enodes.push_back( formula ); // formula needs to be processed
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while ( !unprocessed_enodes.empty() )
  {
    Enode * enode = unprocessed_enodes.back();
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.isDup1( enode ) )
    {
      unprocessed_enodes.pop_back();
      continue;
    }

    bool unprocessed_children = false;

    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; !arg_list->isEnil( )
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only children that haven't been processed yet,
      // but never children of a theory atom
      //
      if ( !egraph.isDup1( arg ) )
      {
	unprocessed_enodes.push_back( arg );
	unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if (unprocessed_children)
      continue;

    unprocessed_enodes.pop_back( );

    if ( !enode->hasSortBool( ) )
    {
      if ( enode->isVar( ) )
	nof_variables ++;
      else if ( enode->isConstant( ) )
      {
	const Real & c = enode->getValue( );
	mpz_lcm( lcm, lcm, c.get_den( ).get_mpz_t( ) );
      }
    }

    assert( !egraph.isDup1( enode ) );
    egraph.storeDup1( enode );
  }

  egraph.doneDup1( );

  Real rescale_factor = Real( mpz_class( lcm )) * Real( nof_variables ) * Real( nof_variables + 1 );
  assert( rescale_factor > 1 );
  //
  // Check if worst-case constants sum excees INT_MAX
  // If so tell the TSolver allocator to use GMP
  //
  curr_constant_sum = 0;
  egraph.initDup1( );
  unprocessed_enodes.push_back( formula );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while ( !unprocessed_enodes.empty() )
  {
    Enode * enode = unprocessed_enodes.back();
    //
    // Skip if the node has already been processed before
    //
    if ( egraph.isDup1( enode ) )
    {
      unprocessed_enodes.pop_back();
      continue;
    }

    bool unprocessed_children = false;

    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; !arg_list->isEnil( )
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only children that haven't been processed yet,
      // but never children of a theory atom
      //
      if ( !egraph.isDup1( arg ) )
      {
	unprocessed_enodes.push_back( arg );
	unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if (unprocessed_children)
      continue;

    unprocessed_enodes.pop_back( );

    if ( !enode->hasSortBool( ) && enode->isConstant( ) )
    {
      Real c = enode->getValue( );
      Real r = c * rescale_factor;

      if ( !egraph.getUseGmp( ) )
      {
	if ( r < 0 )
	  curr_constant_sum += -r + 1;
	else
	  curr_constant_sum +=  r + 1;

	if ( curr_constant_sum > Real( INT_MAX ) 
	  && !egraph.getUseGmp( ) )
	  egraph.setUseGmp( );
      }
    }

    assert( !egraph.isDup1( enode ) );
    egraph.storeDup1( enode );
  }

  egraph.doneDup1( );

  egraph.setRescale( rescale_factor );

  mpz_clear( lcm );
#else
  error( "cannot rescale without GMP", "" );
#endif
}
