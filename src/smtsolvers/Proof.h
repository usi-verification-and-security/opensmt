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

#ifndef PROOF2_H
#define PROOF2_H

#include "Global.h"
#include "CoreSMTSolver.h"
#include "THandler.h"
#include "SolverTypes.h"
#include "TheoryInterpolator.h"

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

    vector< CRef >* chain_cla;               // Clauses chain
    vector< Var > *      chain_var;               // Pivot chain
    int                  ref;                     // Reference counter
    clause_type_t        type;                    // The type of the clause
};

class Proof
{
    bool begun; // For debugging

    vector< CRef > *            chain_cla;
    vector< Var > *             chain_var;
    map< CRef, ProofDer * >     clause_to_proof_der;
    CRef                        last_added;
    ClauseAllocator&            cl_al;
    map< CRef, TheoryInterpolator* >  clause_to_itpr;

public:

    Proof ( ClauseAllocator& cl );
    ~Proof( );

    void addRoot    ( CRef, clause_type_t );              // Adds a new root clause
    void setTheoryInterpolator(CRef, TheoryInterpolator*);
    TheoryInterpolator* getTheoryInterpolator(CRef);
    bool isTheoryInterpolator(CRef);
    void beginChain ( CRef );                             // Beginnig of resolution chain
    void resolve    ( CRef, Var );                        // Resolve
    void endChain   ( );                                      // Chain that ended in sat
    void endChain   ( CRef );                             // Last chain refers to clause
    bool deleted    ( CRef );                             // Remove clauses if possible
    void forceDelete( CRef );         // Remove unconditionally
    inline Clause& getClause        ( CRef cr ) { return cl_al[cr]; } // Get clause from reference

    void pushBacktrackPoint     ( );                          // Restore previous state
    void popBacktrackPoint      ( );                          // Restore previous state
    void reset                  ( );                          // Reset proof data structures

    inline CRef last        ( ) { return last_added; }    // Return last clause added

    inline bool     checkState  ( ) { return !begun; }        // Stupid check

    void print( ostream &, CoreSMTSolver &, THandler & );     // Print proof in SMT-LIB format

    map< CRef, ProofDer * > & getProof( ) { return clause_to_proof_der; }
};

//=================================================================================================

#endif
