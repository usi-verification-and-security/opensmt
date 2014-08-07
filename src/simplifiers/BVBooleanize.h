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

#ifndef BV_BOOLEANIZE_HH
#define BV_BOOLEANIZE_HH

#include "Global.h"
#include "Otl.h"
#include "Egraph.h"

class BVBooleanize
{
public:

  BVBooleanize ( Egraph & egraph_, SMTConfig & config_ )
   : egraph ( egraph_ )
   , config ( config_ )
  { }

  virtual ~BVBooleanize( ) { }

  Enode * doit      ( Enode * );              // Main routine

private:

  Enode * propagateExtract     ( Enode * );   // Propagate extractions
  Enode * propagateExtractRec  ( Enode * );   // Propagate extractions recursively
  Enode * propagateBoolcast    ( Enode * );   // Propagate Boolcasts
  Enode * propagateBoolcastRec ( Enode * );   // Propagate Boolcasts recursively
  Enode * replaceWithTypeCasts ( Enode * );   // Add boolcasts
  Enode * rewriteRules         ( Enode * );   // Apply some rewrite rules
  Enode * removeCasts          ( Enode * );   // Remove remaining casts 
                                              
  Egraph &    egraph;                         // Reference to Egraph
  SMTConfig & config;                         // Reference to Config
                                            
  map< enodeid_t, Enode * > extraction_cache; // Cache for extraction propagation
  map< enodeid_t, Enode * > boolcast_cache;   // Cache for boolcast propagation
};

#endif
