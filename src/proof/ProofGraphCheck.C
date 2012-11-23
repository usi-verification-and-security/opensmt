/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

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
