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

#ifndef AXDIFFPREPROC2_H
#define AXDIFFPREPROC2_H

#include "Global.h"
#include "Otl.h"
#include "Egraph.h"
#include "SStore.h"

class AXDiffPreproc2
{
public:

  AXDiffPreproc2( Egraph & egraph_
                , SStore & sstore_
	        , SMTConfig & config_ )
   : array_eqs_processed ( 0 )
   , fresh_count         ( egraph_.nofEnodes( ) + 1 )
   , egraph              ( egraph_ )
   , sstore              ( sstore_ )
   , config              ( config_ )
  { }

  virtual ~AXDiffPreproc2( ) { }

  Enode * doit ( Enode *, const uint64_t = 0 ); // Main routine

private:

  Enode * gauss        ( Enode * );
  Enode * simplifyEq   ( set< Enode * > &
                       , Enode *
                       , list< Enode * > & );

  Enode * retrieveTopLevelEqs( Enode *
                             , vector< Enode * > & 
                             , vector< Enode * > & );

  void    retrieveTopLevelIndexNeqs( Enode * );
  Enode * solveReflexArrayEquations( Enode * );

  Enode * elimination     ( Enode *, vector< Enode * > &, vector< Enode * > & );
  Enode * substitute      ( Enode *, map< Enode *, Enode * > & );
  Enode * canonize        ( Enode * );
  Enode * canonizeTerm    ( Enode * );
  Enode * canonizeTerm    ( Enode *, set< Enode * > &, Enode * );
  Enode * solve           ( Enode *, list< Enode * > & );

  Enode * simplifyStore   ( Enode * );
  Enode * simplifyStoreEq ( Enode * );

  Enode * flatten         ( Enode * );             // Flatten
  bool    checkFlattened  ( Enode * );
  Enode * addAxioms       ( Enode * );
                          
  Enode * deflatten       ( Enode * );             // Inverse of flattening
                          
  Enode * getFlat         ( Enode *
                          , list< Enode * > & );

  Enode * freshVarFrom    ( Enode * );

  Enode * addNeqAxioms    ( Enode * );             // Simulates preprocessing
  Enode * addNeqAxiom     ( Enode *, Enode *, list< Enode * > & );          

  Enode * addEqualities   ( Enode * );          // Adds index equalities

  void    gatherIndexes   ( Enode * );          // Gather index variables
  void    gatherArrayVars ( Enode * );          // Gather meaningful ax vars

  map< Enode *, Enode * > definitions;          // From term to flat constant
  map< Enode *, Enode * > diff_to_ind;          // Stores already identified diffs
  set< Enode * >          index_variables;      // Set of index variables
  set< Enode * >          new_indexes;          // Indexes added later on 
  vector< Enode * >       array_eqs;            // Set of array equalities

  set< Enode * >          flat_select;          // Selects for which no eq should be created
  set< Enode * >          non_top_array_eqs;
  set< Enode * >          eqs_seen;             // To avoid repetition
  set< Enode * >          write_indexes;        // Set of index variables occ. in writes
  set< Enode * >          array_vars;           // Set of index variables occ. in array eqs
  set< Enode * >          top_neg_indexes;      // Set of top-level differences of indexes
                                                
  size_t         array_eqs_processed;  
  unsigned       fresh_count;                   // Counter to ensure fresh vars
  uint64_t       partition;
  Egraph &	 egraph;                        // Reference to Egraph
  SStore &	 sstore;                        // Reference to SStore
  SMTConfig &	 config;                        // Reference to Config
};

#endif
