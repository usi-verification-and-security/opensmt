/*********************************************************************
 Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>
       , Aliaksei Tsitovich  <aliaksei.tsitovich@usi.ch>
       , Edgar Pek           <edgar.pek@usi.ch>

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
