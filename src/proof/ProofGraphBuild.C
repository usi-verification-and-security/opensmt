/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

OpenSMT -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

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

// Resolution proof builder
void
ProofGraph::buildProofGraph( Proof & proof
                             , set< int >& axioms_ids
                             , int final_root_id
                             , clauseid_t goal
                             , int nVars )
{
  // FIXME: remove these !
  (void)axioms_ids;
  (void)final_root_id;
  (void)goal;
  if ( verbose() )
  {
    cout << "# Building proof graph" << endl;
  }
  const double initTime=cpuTime();

  av_cla_size=0; max_cla_size=0;
  dim_unsat_core=0;
  num_edges=0;
  num_nodes=0;
  num_leaves=0;
  building_time=0;

  // Resolution tree for clause id; pairs <clause,pivot>
  // Structure:
  // a -
  // b c
  // ...
  // a,b resolved over c...
  map< Clause *, ProofDer * > & clause_to_proof_der = proof.getProof( );
  map< Clause *, ProofDer * >::iterator it;

  //To map clauses to graph id
  //An id is associated when the node is created
  map< Clause *, int > clauseToIDMap;

  //To keep track of visited nodes
  set< Clause * > visitedSet;

  //Queue to build proof graph from sink
  std::deque< Clause * > q;

  int currId         = 0
      , lastInternalId = 0
      , id             = 0
      , id0            = 0
      , id1            = 0;

  ProofNode * n = NULL;

  unsigned long num_clause = 0;

#ifdef MEMVERB
  uint64_t mem_used = memUsed();
  uint64_t mem_used_old;
  reportf( "# Memory used before building proof: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
#endif

  //NOTE: first antecedent -> positive occurrence pivot
  // second antecedent -> negative occurrence pivot

  //Start from empty clause
  q.push_back(NULL);
  do
  {
    //Get current clause
    Clause* currClause=q.back();
    q.pop_back();

    //Clause not visited yet
    if(visitedSet.find(currClause)==visitedSet.end())
    {
      //Get clause derivation tree
      ProofDer &           proofder = *(clause_to_proof_der[currClause]);
      vector< Clause * > & chaincla = (*(proofder.chain_cla));            // Clauses chain
      vector< Var > &      chainvar = (*(proofder.chain_var));            // Pivot chain
      clause_type_t        ctype    = proofder.type;

      // No derivation tree: theory lemma or original clause
      // Non empty clause
      if ( ctype==CLA_ORIG || ctype==CLA_THEORY )
      {
        assert(chaincla.size()==0 || chaincla.size()==1);
        assert(currClause!=NULL);

        //Strange case clause with link
        if(chaincla.size()>0)
        {
          if(produceInterpolants()>0)
            solver.setInterpolant( currClause, solver.getInterpolants( chaincla[0] ) );
        }
        //Clause not processed yet
        if(clauseToIDMap.find(currClause)==clauseToIDMap.end())
        {
          n=new ProofNode();
          n->getClause().reserve((*currClause).size());
          for(int k=0;k<(*currClause).size();k++)
            n->getClause().push_back((*currClause)[k]);
          //Add node to graph vector
          currId=(int)graph.size();
          n->setId(currId);
          graph.push_back(n);
          assert(graph[currId]==n);
          //Update map clause->id
          clauseToIDMap[currClause]=currId;
        }
        // NB: internal derived clauses not considered here
        //Original clause
        if(ctype==CLA_ORIG)
        {
          graph[clauseToIDMap[currClause]]->setType(CLAORIG);
          //Determine partition mask in case of interpolation
          if( produceInterpolants() > 0 )
          {
            graph[clauseToIDMap[currClause]]->setInterpPartitionMask( solver.getIPartitions( currClause ) );
            // cout << "Associating mask " << graph[clauseToIDMap[currClause]]->partition_mask << " to clause "; printClause(graph[clauseToIDMap[currClause]]);
          }
        }
        // Theory clause
        else if (ctype==CLA_THEORY)
        {
          graph[clauseToIDMap[currClause]]->setType(CLALEMMA);
          //Determine list of partial interpolants in case of theory lemma
          if( produceInterpolants( ) > 0 )
          {
            Enode * partial_interp_list = solver.getInterpolants( currClause );
            assert( partial_interp_list );
            graph[ clauseToIDMap[ currClause ] ]->setPartialInterpolant( partial_interp_list );
          }
        }
      }
      // Learnt clause
      // Resolution tree present
      else if(ctype==CLA_LEARNT)
      {
        assert(chaincla.size() >= 2);
        // No internal deduced nodes
        if ( chaincla.size( ) == 2 )
        {
          assert(chainvar.size()==1);
          // First clause not yet processed
          if(clauseToIDMap.find(chaincla[0])==clauseToIDMap.end())
          {
            n=new ProofNode();

            clause_type_t  _ctype    = (*(clause_to_proof_der[chaincla[0]])).type;
            if( _ctype==CLA_ORIG || _ctype==CLA_THEORY )
            {
              n->getClause().reserve((*chaincla[0]).size());
              for(int k=0;k<(*chaincla[0]).size();k++)
                n->getClause().push_back((*chaincla[0])[k]);
            }

            //Add node to graph vector
            currId=(int)graph.size();
            n->setId(currId);
            graph.push_back(n);
            assert(graph[currId]==n);
            //Update map clause->id
            clauseToIDMap[chaincla[0]]=currId;
            //Add clause to queue
            q.push_back(chaincla[0]);
          }
          if(clauseToIDMap.find(chaincla[1])==clauseToIDMap.end())
          {
            ProofNode* n=new ProofNode();

            clause_type_t _ctype = (*(clause_to_proof_der[chaincla[1]])).type;
            if( _ctype==CLA_ORIG || _ctype==CLA_THEORY )
            {
              n->getClause().reserve((*chaincla[1]).size());
              for(int k=0;k<(*chaincla[1]).size();k++)
                n->getClause().push_back((*chaincla[1])[k]);
            }

            //Add node to graph vector
            currId=(int)graph.size();
            n->setId(currId);
            graph.push_back(n);
            assert(graph[currId]==n);
            //Update map clause->id
            clauseToIDMap[chaincla[1]]=currId;
            //Add clause to queue
            q.push_back(chaincla[1]);
          }
          id0=clauseToIDMap[chaincla[0]];
          id1=clauseToIDMap[chaincla[1]];
          // Clause not yet processed
          if(clauseToIDMap.find(currClause)==clauseToIDMap.end())
          {
            ProofNode* n=new ProofNode();
            //Add node to graph vector
            currId=(int)graph.size();
            n->setId(currId);
            graph.push_back(n);
            assert(graph[currId]==n);
            //Update map clause->id
            clauseToIDMap[currClause]=currId;
          }
          id=clauseToIDMap[currClause];
          // Setting edges, pivot, type
          graph[id]->setAnt1(graph[id0]);
          graph[id]->setAnt2(graph[id1]);
          graph[id]->setPivot(chainvar[0]);
          graph[id]->setType(CLALEARNT);
          //Sink check
          if(currClause==NULL) root=id;
        }
        else
          // Yes internally deduced clauses
        {
          if(clauseToIDMap.find(chaincla[0])==clauseToIDMap.end())
          {
            n=new ProofNode();
            // Contains positive occurrence pivot
            clause_type_t _ctype = (*(clause_to_proof_der[chaincla[0]])).type;
            if( _ctype==CLA_ORIG || _ctype==CLA_THEORY )
            {
              n->getClause().reserve((*chaincla[0]).size());
              for(int k=0;k<(*chaincla[0]).size();k++)
                n->getClause().push_back((*chaincla[0])[k]);
            }

            //Add node to graph vector
            currId=(int)graph.size();
            n->setId(currId);
            graph.push_back(n);
            assert(graph[currId]==n);
            //Update map clause->id
            clauseToIDMap[chaincla[0]]=currId;
            //Add clause to queue
            q.push_back(chaincla[0]);
          }
          for ( size_t i = 1 ; i < chaincla.size() ; i ++ )
          {
            if(clauseToIDMap.find(chaincla[i])==clauseToIDMap.end())
            {
              ProofNode* n=new ProofNode();
              // Contains negative occurrence pivot
              clause_type_t _ctype = (*(clause_to_proof_der[chaincla[i]])).type;
              if( _ctype==CLA_ORIG || _ctype==CLA_THEORY )
              {
                n->getClause().reserve((*chaincla[i]).size());
                for(int k=0;k<(*chaincla[i]).size();k++)
                  n->getClause().push_back((*chaincla[i])[k]);
              }

              //Add node to graph vector
              currId=(int)graph.size();
              n->setId(currId);
              graph.push_back(n);
              assert(graph[currId]==n);
              //Update map clause->id
              clauseToIDMap[chaincla[i]]=currId;
              //Add clause to queue
              q.push_back(chaincla[i]);
            }
            if(i<chaincla.size()-1)
            {
              // Creation new internal deduced node
              n=new ProofNode();
              //Add node to graph vector
              currId=(int)graph.size();
              n->setId(currId);
              n->setType(CLADERIVED);
              n->setPivot(chainvar[i-1]);
              graph.push_back(n);
              assert(graph[currId]==n);

              // Edges creation
              if(i==1)
                // First internal node deduced from first clauses 0 and 1
              {
                id0=clauseToIDMap[chaincla[0]];
                id1=clauseToIDMap[chaincla[1]];
                // Setting edges, type
                graph[currId]->setAnt1(graph[id0]);
                graph[currId]->setAnt2(graph[id1]);
                lastInternalId=currId;
              }
              else
                // Other internal nodes deduced from clause i and last internal node
              {
                id1=clauseToIDMap[chaincla[i]];
                graph[currId]->setAnt1(graph[lastInternalId]);
                graph[currId]->setAnt2(graph[id1]);
                lastInternalId=currId;
              }
            }
            // End tree reached: examining currClause
            else
            {
              id1=clauseToIDMap[chaincla[i]];
              if(clauseToIDMap.find(currClause)==clauseToIDMap.end())
              {
                n=new ProofNode();

                //Add node to graph vector
                currId=(int)graph.size();
                n->setId(currId);
                graph.push_back(n);
                assert(graph[currId]==n);
                //Update map clause->id
                clauseToIDMap[currClause]=currId;
              }
              id=clauseToIDMap[currClause];
              // Setting edges, pivot, type
              // Edges from last clause and last internal node
              graph[id]->setAnt1(graph[lastInternalId]);
              graph[id]->setAnt2(graph[id1]);
              graph[id]->setPivot(chainvar[i-1]);
              graph[id]->setType(CLALEARNT);
              //Sink check
              if(currClause==NULL) root=id;
            }
          }
        }
      }
      //Mark clause as visited
      visitedSet.insert(currClause);

#ifdef MEMVERB
      if( num_clause % 10000 == 0 )
      {
        std::cout << "VISITING CLAUSE " << num_clause << std::endl;
        mem_used_old = mem_used;
        mem_used = memUsed();
        reportf( "# Memory used: +%.3f MB\n",  mem_used == 0 ? 0 : (mem_used - mem_used_old) / 1048576.0 );
      }
      num_clause++;
#endif
    }
  }
  while(!q.empty());

#ifdef MEMVERB
  mem_used = memUsed();
  reportf( "# Memory used after building proof: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
#endif

  if(graph.size()>SIZE_BIT_VECTOR)
  {
    cerr << "# Error: Number of nodes too large: " << graph.size() << " but limit is " << SIZE_BIT_VECTOR <<  endl;
    cerr << "# Error: Increase SIZE_BIT_VECTOR to " << graph.size() <<  endl;
    exit( 1 );
  }

  num_vars_limit=nVars;

  //Keep track of visited nodes
  visited.reset();

  building_time=cpuTime()-initTime;


  // NOTE: temporary check to be removed
  {
    unsigned long num_leaf = 0;
    unsigned long num_inner = 0;
    std::deque<ProofNode*> q;
    ProofNode* n;
    q.push_back(graph[root]);
    do
    {
      n=q.front();
      q.pop_front();
      //End current level, change level and set new end
      if(!visited[n->getId()])
      {
        if(n->ant1!=NULL || n->ant2!=NULL)
        {
          num_inner++;
          // Derived clause should be empty
          assert(n->getClauseSize()==0);
          if(n->ant1!=NULL) q.push_back(n->ant1);
          if(n->ant2!=NULL) q.push_back(n->ant2);
        }
        else
        {
          num_leaf++;
          // Theory or original clause should not be empty
          assert(n->getClauseSize()!=0);
          assert(n->getType()==CLAORIG || n->getType()==CLALEMMA);
        }
        visited[n->id]=true;
      }
    }
    while(!q.empty());
    visited.reset();
    cerr << "# Number leaves " << num_leaf << "  Number inner " << num_inner <<  endl;
  }
}

//TODO Resolution proof destructor
ProofGraph::~ProofGraph()
{
  for(size_t i=0;i<graph.size();i++)
    if(graph[i]!=NULL)removeNode(i);
}


// Remove redundant pieces of the proof graph
//TODO implement destructor for ProofNodeFly
//returns number of redundant nodes removed
int ProofGraph::cleanProofGraph()
{
  // Visit proof graph from root via DFS
  vector<ProofNode*> q;
  q.push_back(graph[root]);
  int counter=0;

  // Determine the reachable part of the graph
  while(!(q.empty()))
  {
    ProofNode* node=q.back();
    // Remove node
    q.pop_back();
    // Node not yet visited
    if(!(visited[node->id]))
    {
      if(node->ant1!=NULL || node->ant2!=NULL)
      {
        //Enqueue antecedents
        if(node->ant1!=NULL)
          q.push_back(node->ant1);
        if(node->ant2!=NULL)
          q.push_back(node->ant2);
      }
      //Mark node as visited
      visited[node->id]=true;
    }
  }

  // Remove the unreachable part of the graph
  for(size_t i=0;i<graph.size();i++)
  {
#ifdef CHECK
    assert(!(visited[i] && graph[i]==NULL));
#endif
    if(!visited[i])
      if(graph[i]!=NULL)
      {
        removeNode(i);
        counter++;
        //cout << "Node " << i << " not reachable anymore has been removed" << endl;
        //assert(false);
      }
  }
  // Visited nodes vector
  visited.reset();
  return counter;
}

//Remove a node from the graph
void ProofGraph::removeNode(clauseid_t vid)
{
  ProofNode* v=graph[vid];
  assert(v!=NULL);

  //Remove v from the list of its antecedents resolvents
  v->ant1=NULL;
  v->ant2=NULL;
  //Remove interpolant, if any
  if(v->partial_interp!=NULL)
  {
    //delete(v->partial_interp);
    v->partial_interp=NULL;
  }
  //Free memory
  delete v;
  //Remove v
  graph[vid]=NULL;
}

// Input: A set of light variables
// Output: Initializes the graph lightVar set with the set of light variables
void ProofGraph::initializeLightVarSet( set< Var > & lightV )
{
  light_vars.swap( lightV );
  lightV.clear( );
}

#endif
