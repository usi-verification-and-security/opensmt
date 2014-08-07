/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

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
