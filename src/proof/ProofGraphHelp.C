/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

OpenSMT -- Copyright (C) 2008 - 2012 Roberto Bruttomesso

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

// Linear merge for resolution
bool ProofGraph::mergeClauses(vector<Lit>& A, vector<Lit>& B, vector<Lit>& res, Var pivot)
{
  res.clear();
  size_t i, j;
  i = 0;
  j = 0;
  bool rep;
  size_t Asize= A.size();
  size_t Bsize= B.size();
  size_t ressize=0;

  //Insert first element
  if(var(A[i])==pivot) i++;
  if(var(B[j])==pivot) j++;
  if(i < Asize && j < Bsize) {
    if (litLess(A[i],B[j])) {
      if(var(A[i])!=pivot){ res.push_back(A[i]); ressize++; }
      i++;
    }
    else {
      if(var(B[j])!=pivot){ res.push_back(B[j]); ressize++; }
      j++;
    }
  }
  else if (i < Asize) {
    if(var(A[i])!=pivot){ res.push_back(A[i]); ressize++; }
    i++;
  }
  else if (j< Bsize) {
    if(var(B[j])!=pivot){ res.push_back(B[j]); ressize++; }
    j++;
  }

  //Insert further elements avoiding repetitions
  while (i < Asize && j < Bsize) {
    if (litLess(A[i],B[j])) {
      rep=(var(A[i])==var(res[ressize-1]) && sign(A[i])==sign(res[ressize-1]));
      if(var(A[i])!=pivot && !rep){ res.push_back(A[i]); ressize++; }
      i++;
    } else {
      rep=(var(B[j])==var(res[ressize-1]) && sign(B[j])==sign(res[ressize-1]));
      if(var(B[j])!=pivot && !rep){ res.push_back(B[j]); ressize++; }
      j++;
    }
  }
  if (i < Asize)
    for (size_t p = i; p < Asize; p++)
    {
      rep=(var(A[p])==var(res[ressize-1]) && sign(A[p])==sign(res[ressize-1]));
      if(var(A[p])!=pivot && !rep){ res.push_back(A[p]); ressize++; }
    }
  else if(j < Bsize)
    for (size_t p = j; p < Bsize; p++)
    {
      rep=(var(B[p])==var(res[ressize-1]) && sign(B[p])==sign(res[ressize-1]));
      if(var(B[p])!=pivot && !rep){ res.push_back(B[p]); ressize++; }
    }
  assert(ressize==res.size());
  return true;
}

//
// Prints resolution proof graph to a dot file,
// with proper colors
// If skeleton is true then prints propositional variables, otherwise full SMT formulae
void ProofGraph::printProofAsDotty( ostream & out, bool skeleton )
{
  // Visited nodes vector
  vector< bool > visited_dotty( graph.size( ), false );
  // Visit proof graph from sink via DFS
  vector< ProofNode * > q;
  q.push_back(graph[root]);

  out << "digraph proof {" << endl;

  while( !q.empty( ) )
  {
    ProofNode * node = q.back( );
    // Remove node
    q.pop_back( );
    // Node not yet visited
    if( !visited_dotty.at( node->getId() ) )
    {
      //Clean
      //clauseSort(node->clause);
      // Print node
      //0 if original, 1 if lemma, 2 if axiom inst, 3 if deduced, 4 if magenta
      string typ;
      string color="";
      switch( node->getType() )
      {
      case 0:
      {
        typ = "cls_";
        out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() <<"  :  ";
        //solver.printSMTClause( out, node->getClause(), true );
        if(skeleton) printClause(node, out); else printSMTClause(node, out);
        if( node->getPartialInterpolant( ) )
          out << "\\\\n" << node->getPartialInterpolant( );
        out << "\", color=\"blue\", fontcolor=\"white\", style=\"filled\"]" << endl;
      }
      break;
      case 1:
      {
        typ = "lem_";
        out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() <<"  :  ";
        if(skeleton) printClause(node, out); else printSMTClause(node, out);
        if( node->getPartialInterpolant( ) )
          out << "\\\\n" << node->getPartialInterpolant( );
        out << "\", color=\"green\"";
        out << ", style=\"filled\"]" << endl;
      }
      break;
      case 2:
      {
        typ = "axi_";
        out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() <<"  :  ";
        if(skeleton) printClause(node, out); else printSMTClause(node, out);
        if( node->getPartialInterpolant( ) )
          out << "\\\\n" << node->getPartialInterpolant( );
        out << "\", color=\"red\"";
        out << ", style=\"filled\"]" << endl;
      }
      break;
      case 3:
      {
        typ = "ded_";
        out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() <<"  :  ";
        if( !node->getClause().empty( ) )
        { if(skeleton) printClause(node, out); else printSMTClause(node, out); }
        else out << "+"; // learnt clause
        //out << "\", color=\"grey\"";
        if( node->getPartialInterpolant( ) )
          out << "\\\\n" << node->getPartialInterpolant( );
        out << "\", color=\"grey\"";
        out << ", style=\"filled\"]" << endl;
      }
      break;
      case 4:
      {
        typ = "mag_";
        out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() <<"  :  ";
        if( !node->getClause().empty( ) )
        { if(skeleton) printClause(node, out); else printSMTClause(node, out); }
        else out << "+"; // magenta clause
        if( node->getPartialInterpolant( ) )
          out << "\\\\n" << node->getPartialInterpolant( );
        out << "\", color=\"purple\"";
        out << ", style=\"filled\"]" << endl;
      }
      break;
      case 5:
      {
        typ = "der_";
        out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() <<"  :  ";
        if( !node->getClause().empty( ) )
        { if(skeleton) printClause(node, out); else printSMTClause(node, out); }
        else out << "+"; // internal ded clause clause
        if( node->getPartialInterpolant( ) )
          out << "\\\\n" << node->getPartialInterpolant( );
        out << "\", color=\"orange\"";
        out << ", style=\"filled\"]" << endl;
      }
      break;
      default: typ=""; break;
      }

      // Print edges from parents (if existing)
      string t1,t2;
      ProofNode * r1 = node->getAnt1();
      ProofNode * r2 = node->getAnt2();
      if( r1 != NULL && r2 != NULL)
      {
        switch( r1->getType() )
        {
        case 0: t1 = "cls_"; break;
        case 1: t1 = "lem_"; break;
        case 2: t1 = "axi_"; break;
        case 3: t1 = "ded_"; break;
        case 4: t1 = "mag_"; break;
        case 5: t1 = "der_"; break;
        default: t1 = ""; break;
        }
        switch( r2->getType() )
        {
        case 0: t2 = "cls_"; break;
        case 1: t2 = "lem_"; break;
        case 2: t2 = "axi_"; break;
        case 3: t2 = "ded_"; break;
        case 4: t2 = "mag_"; break;
        case 5: t2 = "der_"; break;
        default: t2 = ""; break;
        }

        out << t1 << r1->getId() << " -> " << typ << node->getId();
        out << " [label=\"(" << node->pivot << ")\", fontsize=10]" << endl;
        out << t2 << r2->getId() << " -> " << typ << node->getId();
        out << " [label=\"(" << node->pivot << ")\", fontsize=10]" << endl;

        // Enqueue parents
        q.push_back( r1 );
        q.push_back( r2 );
      }
      //Mark node as visited
      visited_dotty[ node->getId() ] = true;
    }
  }
  out << "}" << endl;
}

void ProofGraph::printClause(ProofNode* n)
{
  assert(n!=NULL);
  vector<Lit>& cl=n->clause;
  cout << n->id << ": ";
  for(size_t k=0;k<cl.size();k++)
  {
    if(sign(cl[k])) cout << "-";
    cout << var(cl[k]) << " ";
  }
  cout << endl;
}

void ProofGraph::printClause(ProofNode* n, ostream & os)
{
  assert(n!=NULL);
  vector<Lit>& cl=n->clause;
  for(size_t k=0;k<cl.size();k++)
  {
    if(sign(cl[k])) os << "-";
    os << var(cl[k]) << " ";
  }
}

void ProofGraph::printSMTClause( ProofNode * n, ostream & os )
{
  assert( n );
  vector< Lit > & c = n->clause;

  if ( c.size( ) == 0 ) os << "-";
  if ( c.size( ) > 1 ) os << "(or ";
  for ( size_t i = 0 ; i < c.size( ) ; i++ )
  {
    Var v = var(c[i]);
    if ( v <= 1 ) continue;
    Enode * e = thandler->varToEnode( v );
    os << ( sign(c[i]) ? "(not " : "" ) << e << ( sign( c[i] ) ? ") " : " " );
  }
  if ( c.size( ) > 1 ) os << ")";
}

//Calculate graph info
void ProofGraph::getGraphInfo()
{
  //Visit graph from sink keeping track of edges and nodes
  std::deque<ProofNode*> q;
  ProofNode* n;

  av_cla_size=0;
  max_cla_size=0;
  var_cla_size=0;
  dim_unsat_core=0;
  num_nodes=0;
  num_edges=0;
  num_unary=0;
  num_leaves=0;


  q.push_back(graph[root]);
  do
  {
    n=q.front();
    q.pop_front();

    //Node not visited yet
    if(!visited[n->id])
    {
      if(n->ant1!=NULL || n->ant2!=NULL)
      {
        if(n->ant1!=NULL)
        {
          q.push_back(n->ant1);
          num_edges++;
        }
        if(n->ant2!=NULL)
        {
          q.push_back(n->ant2);
          num_edges++;
        }
      }
      else
        num_leaves++;

      //Mark node as visited
      visited[n->id]=true;
      num_nodes++;
      av_cla_size+=n->clause.size();
      if(n->clause.size() > (size_t)max_cla_size) max_cla_size=n->clause.size();
      if(n->type==CLAORIG) dim_unsat_core++;
      if(n->clause.size()==1) {
        num_unary++;
      }

    }
  }
  while(!q.empty());

  av_cla_size/=num_nodes;
  //Calculate sample variance for num resolvents and clause size
  for(size_t i=0;i<graph.size();i++)
    if(graph[i]!=NULL)
    {
      var_cla_size+=pow(graph[i]->clause.size()-av_cla_size,2);
    }
  var_cla_size/=(num_nodes-1);
  //Calculate sample variance for clause size
  visited.reset();

  // Determine actual set of variables
  set<Var> ps;
  for(size_t i=0;i<graph.size();i++)
    if(graph[i]!=NULL && graph[i]->ant1!=NULL && graph[i]->ant2!=NULL)
      ps.insert(graph[i]->pivot);
  num_vars_actual=ps.size();

}

//Input: a vector which will contain the topological sorting of nodes
//Output: a topological sorting antecedents-resolvents
void ProofGraph::topolSortingVec(vector<clauseid_t>& DFS)
{
  vector<clauseid_t>q;
  ProofNode* n;
  DFS.clear();
  clauseid_t c;
  q.push_back(root);
  do
  {
    c=q.back();
    n=graph[c];
    assert(n!=NULL);
    //Node not visited yet
    if(!visited2[c])
    {
      //Enqueue antecedents
      if(n->getAnt1()!=NULL && !visited2[n->getAnt1()->getId()]) q.push_back(n->getAnt1()->getId());
      else if(n->getAnt2()!=NULL && !visited2[n->getAnt2()->getId()]) q.push_back(n->getAnt2()->getId());
      //Mark node as visited if both antecedents visited
      else
      {
        visited2[c]=true;
        q.pop_back();
        DFS.push_back(c);
      }
    }
    else
      q.pop_back();
  }
  while(!q.empty());

  visited2.reset();
}

string ProofGraph::printClauseType(clause_type ct)
{
  string s;
  switch ((int)ct) {
  case 0:
    s = "original";
    break;
  case 1:
    s = "lemma";
    break;
  case 3:
    s = "learnt";
    break;
  case 4:
    s = "magenta";
    break;
  case 5:
    s = "derived";
    break;
  default:
    s = "badvalue";
    break;
  }
  return s;
}

void ProofGraph::printProofNode(clauseid_t vid)
{
  ProofNode* v=graph[vid];
  if(v==NULL)
  {
    cerr << vid << " removed"<< endl<<endl;
    return;
  }
  cerr << "Node id: " << v->id << "   Type: " << v->type;
  if(v->ant1!=NULL && v->ant2!=NULL)
  {
    cerr << "   Parents: " << v->ant1->id << " " << v->ant2->id << "   Pivot: " << v->pivot;
  }
  cerr << "   Clause: ";
  for(size_t i=0;i<v->clause.size();i++)
  {
    if(sign(v->clause[i])) cerr << "~";
    cerr << var(v->clause[i]) << " ";
  }
  cerr << endl;

}

#endif
