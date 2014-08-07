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
