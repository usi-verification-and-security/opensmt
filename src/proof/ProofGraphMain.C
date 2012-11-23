/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

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

#include "ProofGraph.h"

#ifdef PRODUCE_PROOF

// Outputs original proof in dotty format, if reduction enabled also outputs reduced proof in dotty format
void ProofGraph::handleProof( )
{
#ifdef CHECK
  checkProof();
  cleanProofGraph();
  checkProof();
#endif

  assert( produceInterpolants( ) == 0);
  assert( printProofDotty( ) == 1 );

  //Print propositional skeleton or full proof
  const bool skeleton=false;
  if ( printProofDotty() == 1 )
  {
    //Print original proof
    if( verbose() > 0 ) cerr << "# Outputting dotty proof" << endl;
    ofstream dotty( "proof.dot" );
    printProofAsDotty( dotty, skeleton  );
  }
}

// Manipulates proofs and generates sequence of interpolants
void ProofGraph::handleProofInter( )
{
#ifdef CHECK
  checkProof();
  cleanProofGraph();
  checkProof();
#endif

  assert( produceInterpolants() == 1);

  // Print propositional skeleton or full proof
  const bool skeleton = false;
  if( printProofDotty() == 1 )
  {
    //Print original proof
    if( verbose() > 0 ) cerr << "# Outputting dotty proof" << endl;
    ofstream dotty( "proof.dot" );
    printProofAsDotty( dotty, skeleton );
  }

  // Retrieve ABmixed atoms
  solver.getMixedAtoms( light_vars ); 

  // Interpolation phase
  // Makes sense to reorder proof only if there are AB-mixed predicates;
  // notice that attempts to reduction can be embedded inside reordering procedure
  if ( !light_vars.empty( ) )
  {
    // NOTE disabled transformation
    assert(false);
  }
}

#endif
