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


#include "CoreSMTSolver.h"
#include "Proof.h"

#include <unordered_map>


  Proof::Proof( ClauseAllocator& cl )
  : begun     ( false )
  , cl_al		( cl )
{ }

void Proof::newLeafClause(CRef c, clause_type t)
{
    assert(c != CRef_Undef);
    assert(clause_to_proof_der.find(c) == clause_to_proof_der.end());
    clause_to_proof_der.emplace(c, ProofDer{t});
}


//
// This is the beginning of a derivation chain.
//
void Proof::beginChain( CRef c )
{

    assert( c != CRef_Undef );
    assert( !hasOpenChain() );
//    if(c == 497){
//        std::cout<<"Hi!";
//    }
//    printf("BegUN chain %d\n", c);
    begun = true;
    assert(current_chain.isEmpty());
    assert( clause_to_proof_der.find( c ) != clause_to_proof_der.end( ) );
    current_chain.setInitial(c);
    // Increase reference
    ++clause_to_proof_der.at(c).ref;
   }

//
// Store a resolution step with chain_cla.back( ) and c
// on the pivot variable p
//
void Proof::addResolutionStep(CRef c, Var p)
{
    assert(hasOpenChain());
    assert( c != CRef_Undef );
    current_chain.addResolutionStep(c,p);
    assert( clause_to_proof_der.find( c ) != clause_to_proof_der.end( ) );
    // Note that clause c is used as an assumption in another derivation
    clause_to_proof_der.at(c).ref++;
}

// Finalize and store the temporary chain
void Proof::endChain( CRef conclusion )
{
  assert(hasOpenChain());
//  std::cout<<"Has ended chain: " << conclusion << "\n";
//  if(conclusion == 1509){
//      printf("Lol\n");
//  }
  begun = false;
  // There was no chain (only the first clause was stored)
  if ( current_chain.isTrivial() )
  {
      CRef premise = current_chain.chain_cla[0];
      auto premise_type = clause_to_proof_der.at(premise).type; (void)premise_type;
      // MB: When analyzing theory conflict, it might happen that the learnt clause is the same as conflicting clause
      //     (but order of literals might be different)
      assert(premise == conclusion || premise_type == clause_type::CLA_THEORY);
      if (premise != conclusion) {
          // It must be the case that premise is a theory clause and conclusion is an equivalent clause
          // Just create a separate proof chain for conclusion.
          this->newTheoryClause(conclusion);
      }
      assert( clause_to_proof_der.find( conclusion ) != clause_to_proof_der.end( ) );
      // No need to update the chain already stored in the proof
      current_chain.clear();
  }
  else {
      // Otherwise there was a real derivation chain
      // Save the temporary derivation chain in a new
      // derivation structure
      assert(!current_chain.isEmpty());
      assert(current_chain.ref == 0);
      current_chain.type = clause_type::CLA_LEARNT;
      assert( clause_to_proof_der.find( conclusion ) == clause_to_proof_der.end( ) );
      // Create association between res and it's derivation chain
      clause_to_proof_der.emplace(conclusion, std::move(current_chain));
      current_chain.clear();
  }
}

bool Proof::deleted( CRef cr )
{
  // Never remove units
  if ( cl_al[cr].size( ) == 1 ) return false;
  assert( clause_to_proof_der.find( cr ) != clause_to_proof_der.end( ) );
  const ProofDer& d = clause_to_proof_der[ cr ];
  assert( d.ref >= 0 );
  // This clause is still used somewhere else, keep it
  if ( d.ref > 0 ) { return false; }
  // No derivation uses this clause as an assumption, it is safe to remove its derivation.
  // The assumption clauses are notified that there is one less derivation where they are used
  for ( unsigned i = 0 ; i < d.chain_cla.size( ) ; i ++ )
  {
    assert( clause_to_proof_der.find( d.chain_cla[i] ) != clause_to_proof_der.end( ) );
    ProofDer & parent = clause_to_proof_der.at(d.chain_cla[i]);
    parent.ref--;
  }
  assert( d.ref == 0 );
  clause_to_proof_der.erase( cr );
  // The clause itself can be removed from Clause store
  cl_al.free( cr );
  return true;
}

void Proof::print( ostream & out, CoreSMTSolver & s, THandler & t )
{
  if ( clause_to_proof_der.find( CRef_Undef ) == clause_to_proof_der.end( ) )
    opensmt_error( "there is no proof of false" );

  out << "(proof " << endl;

  int nof_lets = 0;

  vector< CRef > unprocessed;
  unprocessed.push_back( CRef_Undef );
  set< CRef > cache;
  set< CRef > core;

  while( !unprocessed.empty( ) )
  {
    CRef cr = unprocessed.back( );
    // Skip already seen
    if ( cache.find( cr ) != cache.end( ) )
    {
      unprocessed.pop_back( );
      continue;
    }
    assert( clause_to_proof_der.find( cr ) != clause_to_proof_der.end( ) );
    ProofDer * d = &clause_to_proof_der.at(cr);

    // Special case in which there is not
    // a derivation but just an equivalence
    if ( d->chain_cla.size( ) == 1 )
    {
      // Say c is done
      cache.insert( cr );
      // Move to equiv
      cr = d->chain_cla[0];
      // Retrieve derivation
      assert( clause_to_proof_der.find( cr ) != clause_to_proof_der.end( ) );
      d = &clause_to_proof_der[ cr ];
    }
    assert( d->chain_cla.size( ) != 1 );
    // Look for unprocessed children
    bool unproc_children = false;
    for ( unsigned i = 0 ; i < d->chain_cla.size( ) ; i ++ )
    {
      CRef cc = d->chain_cla[i];
      if ( cache.find( cc ) == cache.end( ) )
      {
	unproc_children = true;
	unprocessed.push_back( cc );
      }
    }
    // Depth first
    if ( unproc_children )
      continue;
    // Remove current
    unprocessed.pop_back( );

    if ( d->chain_cla.size( ) > 0 )
    {
      out << "; ";
      if ( cr == CRef_Undef )
	out << "-";
      else
	s.printSMTClause( out, cl_al[cr] );
      out << endl;
      out << "(let (cls_" << cr;
      nof_lets ++;

      vector< CRef > & chain_cla = d->chain_cla;
      vector< Var > & chain_var = d->chain_var;

      assert( chain_cla.size( ) == chain_var.size( ) + 1 );

      for ( unsigned i = 1 ; i < chain_cla.size( ) ; i ++ )
	out << " (res";
      for ( unsigned ic = 1, iv = 0 ; iv < chain_var.size( ) ; ic ++, iv ++ )
      {
	if ( ic == 1 )
	{
	  assert( iv == 0 );
	  out << " cls_" << chain_cla[ 0 ]
	    << " cls_" << chain_cla[ 1 ]
	    << " " << t.getVarName(chain_var[0])
	    << ")";
	}
	else
	{
	  out << " cls_" << chain_cla[ ic ]
	    << " " << t.getVarName(chain_var[iv])
	    << ")";
	}
      }
      out << ")" << endl;
    }
    else
    {
      if ( d->type == clause_type::CLA_ORIG )
	core.insert( cr );
      else if ( d->type == clause_type::CLA_THEORY ) { }
      else { }
      out << "(let (cls_" << cr << " ";
      s.printSMTClause( out, cl_al[cr] );
      out << ")" << endl;
      nof_lets ++;
    }

    cache.insert( cr );
  }

  out << "cls_0"  << endl;

  for ( int i = 0 ; i < nof_lets ; i ++ )
    out << ")";
  out << endl;

  out << ":core" << endl;
  out << "( ";
  for ( set< CRef >::iterator it = core.begin( )
      ; it != core.end( )
      ; it ++ )
  {
    out << "cls_" << *it << " ";
  }
  out << ")" << endl;
  out << ")" << endl;
}

void Proof::cleanAssumedLiteral(Lit l) {
    CRef unit = assumed_literals.at(l);
    assert(clause_to_proof_der.find(unit) != clause_to_proof_der.end());
    clause_to_proof_der.erase(unit);
    cl_al.free(unit);
}

//=============================================================================
// The following functions are declared in CoreSMTSolver.h

void CoreSMTSolver::printProofSMT2( ostream & out )
{ proof->print( out, *this, theory_handler ); }

std::ostream & operator<<(std::ostream & os, clause_type val) {
    switch (val){
        case clause_type ::CLA_LEARNT:
            os << "learnt";
            break;
        case clause_type ::CLA_DERIVED:
            os << "derived";
            break;
        case clause_type ::CLA_ORIG:
            os << "original";
            break;
        case clause_type ::CLA_THEORY:
            os << "theory";
            break;
        default:
            assert(false);
    }
    return os;
}

