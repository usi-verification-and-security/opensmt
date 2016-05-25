/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso


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

#ifndef SMTCOMP
void CoreSMTSolver::dumpCNF( )
{
  const char * name = "cnf.smt2";
  std::ofstream dump_out( name );
//  egraph.dumpHeaderToFile( dump_out );
  dump_out << "(assert" << endl;
  dump_out << "(and" << endl;

  for ( int i = 0 ; i < clauses.size( ) ; i ++ )
  {
    Clause & c = ca[clauses[i]];

    if ( c.mark( ) == 1 )
      continue;

//    printSMTClause( dump_out, c );
    dump_out << endl;
  }

  //
  // Also dump the trail which contains clauses of size 1
  //
  for ( int i = 0 ; i < trail.size( ) ; i ++ )
  {
    Var v = var(trail[i]);
    if ( v <= 1 ) continue;
//    Enode * e = theory_handler->varToEnode( v );
//    dump_out << (sign(trail[i])?"(not ":" ") << e << (sign(trail[i])?") ":" ") << endl;
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
    assert(ca[clauses[i]].mark() == 0);
    Clause& c = ca[clauses[i]];
    for (int j = 0; j < c.size(); j++)
      if (modelValue(c[j]) == l_True)
	goto next;

    reportf("unsatisfied clause: ");
    printClause<Clause>(ca[clauses[i]]);
//    printSMTClause( cerr, *clauses[i] );
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
    if (ca[clauses[i]].mark() == 0)
      cnt += ca[clauses[i]].size();

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
//  egraph.printModel( config.getRegularOut( ) );
}

void CoreSMTSolver::printModel( ostream & out )
{
  for (Var v = 2; v < model.size(); v++)
  {
//    Enode * e = theory_handler->varToEnode( v );
//    if ( e->isTAtom( ) )
//      continue;
    int tmp1, tmp2;
//    if( sscanf( (e->getCar( )->getName( )).c_str( ), CNF_STR, &tmp1, &tmp2 ) != 2 )
 //     if ( model[ v ] != l_Undef )
//	out << ( model[ v ] == l_True ? "" : "(not " ) << e << ( model[ v ] == l_True ? "" : ")" ) << endl;
  }
}
#endif
