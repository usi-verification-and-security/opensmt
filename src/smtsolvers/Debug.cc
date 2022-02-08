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

void CoreSMTSolver::dumpCNF( )
{
  const char * name = "cnf.smt2";
  std::ofstream dump_out( name );
//  egraph.dumpHeaderToFile( dump_out );
  dump_out << "(assert" << '\n';
  dump_out << "(and" << '\n';

  for ( int i = 0 ; i < clauses.size( ) ; i ++ )
  {
    Clause & c = ca[clauses[i]];

    if ( c.mark( ) == 1 )
      continue;

//    printSMTClause( dump_out, c );
    dump_out << '\n';
  }

  dump_out << "))" << '\n';
  dump_out << "(check-sat)" << '\n';
  dump_out << "(exit)" << '\n';
  dump_out.close( );
  std::cerr << "[Dumped " << name << "]" << '\n';
}

void CoreSMTSolver::verifyModel()
{
    bool failed = false;
    for (int i = 0; i < clauses.size(); i++)
    {
        assert(ca[clauses[i]].mark() == 0);
        Clause& c = ca[clauses[i]];
        for (unsigned j = 0; j < c.size(); j++)
            if (modelValue(c[j]) == l_True)
                goto next;

        reportf("unsatisfied clause: ");
        printClause<Clause>(ca[clauses[i]]);
        reportf("\n");
        failed = true;
        next:;
    }

    assert(!failed); (void)failed;

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
    printLit(trail[i]);
    std::cerr << ' ' << (sign(trail[i]) ? "not " : "")
        << theory_handler.getLogic().printTerm(theory_handler.varToTerm(var(trail[i]))) << '\n';
  }
}

