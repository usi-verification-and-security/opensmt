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

#ifndef PROOF2_H
#define PROOF2_H

#include "Global.h"
#include "CoreSMTSolver.h"
#include "THandler.h"
#include "SolverTypes.h"

//=================================================================================================

class CoreSMTSolver;
class THandler;

typedef enum { CLA_ORIG, CLA_LEARNT, CLA_THEORY } clause_type_t;

struct ProofDer
{
	ProofDer( )
	: chain_cla ( NULL )
	, chain_var ( NULL )
	, ref       ( 0 )
	{ }

	~ProofDer( )
	{
		assert( chain_cla );
		delete chain_cla;
		if ( chain_var ) delete chain_var;
	}

	vector< Clause * > * chain_cla;               // Clauses chain
	vector< Var > *      chain_var;               // Pivot chain
	int                  ref;                     // Reference counter
	clause_type_t        type;                    // The type of the clause
};

class Proof 
{
	bool begun;					// For debugging

	vector< Clause * > *        chain_cla;
	vector< Var > *             chain_var;
	map< Clause *, ProofDer * > clause_to_proof_der;
	Clause *                    last_added;

public:

	Proof ( );
	~Proof( );

	void addRoot    ( Clause *, clause_type_t );              // Adds a new root clause
	void beginChain ( Clause * );                             // Beginnig of resolution chain
	void resolve    ( Clause *, Var );                        // Resolve
	void endChain   ( );                                      // Chain that ended in sat
	void endChain   ( Clause * );                             // Last chain refers to clause
	bool deleted    ( Clause * );                             // Remove clauses if possible
	void forceDelete( Clause *, const bool = false );         // Remove unconditionally

	void pushBacktrackPoint     ( );                          // Restore previous state
	void popBacktrackPoint      ( );                          // Restore previous state
	void reset                  ( );                          // Reset proof data structures

	inline Clause * last        ( ) { return last_added; }    // Return last clause added

	inline bool     checkState  ( ) { return !begun; }        // Stupid check

	void print( ostream &, CoreSMTSolver &, THandler & );     // Print proof in SMT-LIB format

	map< Clause *, ProofDer * > & getProof( ) { return clause_to_proof_der; }
};

//=================================================================================================

#endif
