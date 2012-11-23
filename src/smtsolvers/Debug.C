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

#include "CoreSMTSolver.h"

#ifndef SMTCOMP
void CoreSMTSolver::dumpCNF( )
{
  const char * name = "cnf.smt2";
  std::ofstream dump_out( name );
  egraph.dumpHeaderToFile( dump_out );
  dump_out << "(assert" << endl;
  dump_out << "(and" << endl;

  for ( int i = 0 ; i < clauses.size( ) ; i ++ )
  {
    Clause & c = *clauses[ i ];

    if ( c.mark( ) == 1 )
      continue;

    printSMTClause( dump_out, c );
    dump_out << endl;
  }

  //
  // Also dump the trail which contains clauses of size 1
  //
  for ( int i = 0 ; i < trail.size( ) ; i ++ )
  {
    Var v = var(trail[i]);
    if ( v <= 1 ) continue;
    Enode * e = theory_handler->varToEnode( v );
    dump_out << (sign(trail[i])?"(not ":" ") << e << (sign(trail[i])?") ":" ") << endl;
  }

  dump_out << "))" << endl;
  dump_out << "(check-sat)" << endl;
  dump_out << "(exit)" << endl;
  dump_out.close( );
  cerr << "[Dumped " << name << "]" << endl;
}

void CoreSMTSolver::verifyModel()
{
  bool failed = false;
  for (int i = 0; i < clauses.size(); i++)
  {
    assert(clauses[i]->mark() == 0);
    Clause& c = *clauses[i];
    for (int j = 0; j < c.size(); j++)
      if (modelValue(c[j]) == l_True)
	goto next;

    reportf("unsatisfied clause: ");
    printClause(*clauses[i]);
    printSMTClause( cerr, *clauses[i] );
    reportf("\n");
    failed = true;
next:;
  }

  assert(!failed);

  // Removed line
  // reportf("Verified %d original clauses.\n", clauses.size());
}

void CoreSMTSolver::checkLiteralCount()
{
  // Check that sizes are calculated correctly:
  int cnt = 0;
  for (int i = 0; i < clauses.size(); i++)
    if (clauses[i]->mark() == 0)
      cnt += clauses[i]->size();

  if ((int)clauses_literals != cnt){
    fprintf(stderr, "literal count: %d, real value = %d\n", (int)clauses_literals, cnt);
    assert((int)clauses_literals == cnt);
  }
}

void CoreSMTSolver::printTrail( )
{
  for (int i = 0; i < trail.size(); i++)
  {
    printLit( trail[i] );
    // cerr << " | ";
    // printSMTLit( cerr, trail[i] );
    cerr << endl;
  }
}

void CoreSMTSolver::printModel( )
{
  // Print Boolean model
  printModel( config.getRegularOut( ) );
  // Print Theory model
  egraph.printModel( config.getRegularOut( ) );
}

void CoreSMTSolver::printModel( ostream & out )
{
  for (Var v = 2; v < model.size(); v++)
  {
    Enode * e = theory_handler->varToEnode( v );
    if ( e->isTAtom( ) )
      continue;
    int tmp1, tmp2;
    if( sscanf( (e->getCar( )->getName( )).c_str( ), CNF_STR, &tmp1, &tmp2 ) != 2 )
      if ( model[ v ] != l_Undef )
	out << ( model[ v ] == l_True ? "" : "(not " ) << e << ( model[ v ] == l_True ? "" : ")" ) << endl;
  }
}
#endif
