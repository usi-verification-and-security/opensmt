/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

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

#include "Purify.h"

void
Purify::doit( Enode * formula )
{
  assert( config.logic == QF_UFIDL
       || config.logic == QF_UFLRA );

  // It works as follows:
  // the formula is not actually purified, as it
  // should be in a textbook version of the algorithm.
  // Instead we just traverse the formula, and we collect
  // the terms that would have to become interface 
  // variables

  egraph.gatherInterfaceTerms( formula );
}

void
Purify::doit( vector< Enode * > & assertions )
{
#ifdef PRODUCE_PROOF
  assert( config.produce_inter != 0 );
#endif
  for ( size_t i = 0 ; i < assertions.size( ) ; i ++ )
    egraph.gatherInterfaceTerms( assertions[ i ] );
}
