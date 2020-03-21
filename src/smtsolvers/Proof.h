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

#include "SolverTypes.h"
#include <vector>
#include <unordered_map>
#include <iosfwd>

//=================================================================================================

class CoreSMTSolver;
class THandler;

/**
 * 4 types of clauses:
 * - original -> part of the propositional skeleton of the original input
 * - theory   -> theory-valid clause; not part of the original input, but adding it results in T-equivalent formula
 * - learnt   -> clause learnt by the SAT solver, result of a derivation chain
 * - derived  -> denotes intermediate clauses in resolution chains; needed only for ProofGraph (consider removing it)
 */
enum class clause_type: char { CLA_ORIG, CLA_LEARNT, CLA_THEORY, CLA_DERIVED, CLA_ASSUMPTION };
inline bool isLeafClauseType(clause_type ct) {
    return ct == clause_type::CLA_ORIG || ct == clause_type::CLA_THEORY || ct == clause_type::CLA_ASSUMPTION;
}

std::ostream &operator<<(std::ostream &os, clause_type enumTmp);

/**
 * Helper structure for representing derivation of a clause. The clause derived is not stored here, but in the proof.
 * If this represents a proper resolution from assumptions, then number of clauses must be 1 + number of vars
 * and for each i, variables chain_var[i] is a pivot of a resolution between chain_cla[i] and chain_cla[i+1]
 */
struct ProofDer
{
    ProofDer() : ref {0}, type{clause_type::CLA_ORIG} {}
    ProofDer(clause_type type) : ref {0}, type{type} {}

    ~ProofDer( ) = default;

    std::vector< CRef >  chain_cla;               // Clauses chain
    std::vector< Var >   chain_var;               // Pivot chain
    int                  ref;                     // Reference counter
    clause_type          type;                    // The type of the clause

    bool isEmpty() const { return chain_cla.empty() && chain_var.empty(); }
    void setInitial(CRef c) { chain_cla.push_back(c); }
    bool isTrivial() const { return chain_cla.size() == 1 && chain_var.empty(); }
    void clear() { chain_cla.clear(); chain_var.clear(); ref = 0; }
    void addResolutionStep(CRef c, Var v) { chain_cla.push_back(c), chain_var.push_back(v); }
};


class Proof
{
    bool begun; // For debugging

    ProofDer current_chain;
    std::unordered_map< CRef, ProofDer>     clause_to_proof_der;
    ClauseAllocator&            cl_al;

public:

    Proof ( ClauseAllocator& cl );
    ~Proof( ) = default;

    // Notifies the proof about a new original clause.
    void newOriginalClause ( CRef);

    // Notifies the proof about a new T-clause.
    void newTheoryClause ( CRef);

    // Notifies the proof about an assumption-literal unit clause needed in the proof
    void newAssumptionLiteral(CRef);

    // Notifies the proof that a new resolution chain, starting from the passed clause, is being processed.
    void beginChain ( CRef );

    // Notifies the proof that the current resolution chain has ended with the passed clause.
    void endChain   ( CRef );

    // Notifies the proof to register a resolution step in current chain.
    void addResolutionStep( CRef, Var );

    inline bool hasOpenChain() { return begun; }

    bool deleted    ( CRef );                             // Remove clauses if possible
    inline Clause& getClause        ( CRef cr ) { return cl_al[cr]; } // Get clause from reference

    void print( std::ostream &, CoreSMTSolver &, THandler & );     // Print proof in SMT-LIB format

    std::unordered_map< CRef, ProofDer> & getProof( ) { return clause_to_proof_der; }
};

//=================================================================================================

#endif
