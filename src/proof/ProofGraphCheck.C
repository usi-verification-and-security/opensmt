/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

OpenSMT2 -- Copyright (C) 2008 - 2012 Roberto Bruttomesso

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

//Checks for various issues
//return false if issues present
void ProofGraph::checkClause(clauseid_t nid)
{
	ProofNode* n=graph[nid];
	assert(n!=NULL);
	assert(n->getId()==nid);

	//Check if empty clause
	if(n->getId()==root)
	{
		if(n->clause.size()!=0)
		{
			cerr << n->getId() << " is the sink but not an empty clause" << endl;
			printClause(n);
			assert(false);
		}
	}
	if(n->getClauseSize()==0)
	{
		if(n->getType()==CLAORIG || n->getType()==CLALEMMA)
		{
			cerr << n->getId() << " is an empty original or lemma clause" << endl;
			assert(false);
		}
	}

	if(n->ant1==NULL && n->ant2!=NULL)
	{
		cerr << "Antecedent 1 null" << endl;
		assert(false);
	}
	if(n->ant1!=NULL && n->ant2==NULL)
	{
		cerr << "Antecedent 2 null" << endl;
		assert(false);
	}

	if(n->ant1!=NULL && n->ant2!=NULL)
	{
		assert(n->id != n->ant1->id && n->id !=n->ant2->id);

		vector<Lit> v;
		mergeClauses(n->ant1->clause,n->ant2->clause,v,n->pivot);
		if(v.size()!=n->clause.size())
		{
			cerr << "Clause : "; printClause(graph[nid]); cout << " does not correctly derive from antecedents " << endl;
			printClause(graph[n->ant1->id]);
			printClause(graph[n->ant2->id]);
			assert(false);
		}
		for(size_t i=0;i<n->clause.size();i++)
			if(!litEq(n->clause[i],v[i]))
			{
				cerr << "Clause : "; printClause(graph[nid]); cout << " does not correctly derive from antecedents " << endl;
				printClause(graph[n->ant1->id]);
				printClause(graph[n->ant2->id]);
				assert(false);
			}
		assert(graph[n->ant1->id]!=NULL);
		assert(graph[n->ant2->id]!=NULL);
	}
}

//Checks that the proof graph has no issues
void ProofGraph::checkProof()
{
	//Visit graph from sink keeping track of edges and nodes
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
			checkClause(n->getId());
			if(n->getAnt1()!=NULL || n->getAnt2()!=NULL)
			{
				if(n->getAnt1()!=NULL) q.push_back(n->getAnt1());
				if(n->getAnt2()!=NULL) q.push_back(n->getAnt2());
			}
			visited[n->getId()]=true;
		}
	}
	while(!q.empty());
	visited.reset();
}

#endif
