/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

Periplo -- Copyright (C) 2013, Simone Fulvio Rollini

Periplo is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Periplo is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Periplo. If not, see <http://www.gnu.org/licenses/>.
 *********************************************************************/


#ifdef PRODUCE_PROOF
#include "PG.h"
#include <sys/wait.h>


void ProofGraph::verifyLeavesInconsistency( )
{
	if( verbose() > 0 ) { cerr << "# Verifying unsatisfiability of the set of proof leaves" << endl; }

	vector<clauseid_t> proofleaves;
	clauseid_t id,id1,id2;
	vector<clauseid_t> q;
	ProofNode * node = NULL;
	std::vector<unsigned>* visited_count_ = new vector<unsigned>(getGraphSize(),0);
	std::vector<unsigned>& visited_count = *visited_count_;
	// Building DFS vector
	q.push_back(getRoot()->getId());
	do
	{
		id = q.back();
		node = getNode(id);
		assert(node);
		visited_count[id]++;
		q.pop_back();

		// All resolvents have been visited
		if(id == getRoot()->getId() || visited_count[id] == node->getNumResolvents())
		{
			if(!node->isLeaf())
			{
				id1 = node->getAnt1()->getId();
				id2 = node->getAnt2()->getId();
				// Enqueue antecedents
				assert( visited_count[id1] < node->getAnt1()->getNumResolvents() );
				assert( visited_count[id2] < node->getAnt2()->getNumResolvents() );
				q.push_back(id1); q.push_back(id2);
			}
			else proofleaves.push_back(id);
		}
	}
	while(!q.empty());
	delete visited_count_;

	// First stage: print declarations
	const char * name = "verifyinconsistency_leaves.smt2";
	ofstream dump_out( name );
	logic_.dumpHeaderToFile( dump_out );

	unsigned added = 0;
	for ( int i = 0 ; i < proofleaves.size( ) ; i ++ )
	{
		if(added == 0)
		{
			dump_out << "(assert " << endl;
			dump_out << "(and" << endl;
			added++;
		}
		solver.printSMTClause( dump_out, getNode(proofleaves[ i ])->getClause(), false );
		dump_out << endl;
	}
	if(added > 0) dump_out << "))" << endl;

	dump_out << "(check-sat)" << endl;
	dump_out << "(exit)" << endl;
	dump_out.close( );

	// Check !
	bool tool_res;
	if ( int pid = fork() )
	{
		int status;
		waitpid(pid, &status, 0);
		switch ( WEXITSTATUS( status ) )
		{
		case 0:
			tool_res = false;
			break;
		case 1:
			tool_res = true;
			break;
		default:
			perror( "# Error: Certifying solver returned weird answer (should be 0 or 1)" );
			exit( EXIT_FAILURE );
		}
	}
	else
	{
		execlp( config.certifying_solver, config.certifying_solver, name, NULL );
		perror( "Error: Certifying solver had some problems (check that it is reachable and executable)" );
		exit( EXIT_FAILURE );
	}
	if ( tool_res == true )
		opensmt_error( "External tool says the set of proof leaves is satisfiable" );

	remove(name);
}


bool ProofNode::checkPolarityAnt()
{
	assert(getAnt1()); assert(getAnt2());
	vector<Lit>& cla = getAnt1()->getClause();
	for(size_t i=0; i<cla.size() ;i++)
		if(var(cla[i])==getPivot())
		{
			if(sign(cla[i])) return false;
			else return true;
		}
	opensmt_error_();
}

void ProofGraph::checkClauseSorting(clauseid_t nid)
{
	ProofNode* n=getNode(nid);
	assert(n);
	assert(n->getId()==nid);

	if(n->getClauseSize()==0)return;

	for(size_t i=0;i<n->getClauseSize()-1;i++)
	{
		if(var(n->getClause()[i]) > var(n->getClause()[i+1]))
		{
			cerr << "Bad clause sorting for clause " << n->getId() << " of type " << n->getType() << endl;
			printClause(n);
			opensmt_error_();
		}
		if(var(n->getClause()[i])==var(n->getClause()[i+1]) && sign(n->getClause()[i])==sign(n->getClause()[i+1]))
		{
			cerr << "Repetition of var " << var(n->getClause()[i]) << " in clause " << n->getId() << " of type " << n->getType() << endl;
			printClause(n);
			opensmt_error_();
		}
		if(var(n->getClause()[i])==var(n->getClause()[i+1]) && sign(n->getClause()[i])!=sign(n->getClause()[i+1]))
		{
			cerr << "Inconsistency on var " << var(n->getClause()[i]) << " in clause " << n->getId() << " of type " << n->getType() << endl;
			printClause(n);
			opensmt_error_();
		}
	}
}

void ProofGraph::checkClause(clauseid_t nid)
{
	ProofNode* n=getNode(nid);
	assert(n);
	assert(n->getId()==nid);

	//Check if empty clause
	if(isRoot(n))
	{
		if(n->getClauseSize()!=0)
		{
			cerr << n->getId() << " is the sink but not an empty clause" << endl;
			printClause(n);
			opensmt_error_();
		}
	}
	if(n->getClauseSize()==0)
	{
		if(n->getType()==CLAORIG)
		{
			cerr << n->getId() << " is an empty original clause" << endl;
			opensmt_error_();
		}
	}
	else checkClauseSorting(n->getId());

	if(!n->isLeaf())
	{
		assert(n->getId() != n->getAnt1()->getId() && n->getId() !=n->getAnt2()->getId());
		assert(getNode(n->getAnt1()->getId()));
		assert(getNode(n->getAnt2()->getId()));

		if(n->getClauseSize()!=0)
		{
			vector<Lit>* v_ = new vector<Lit>();
			vector<Lit>& v = *v_;
			mergeClauses(n->getAnt1()->getClause(),n->getAnt2()->getClause(),v,n->getPivot());
			if(v.size()!=n->getClauseSize())
			{
				cerr << "Clause : "; printClause(n); cerr << " does not correctly derive from antecedents " << endl;
				printClause(getNode(n->getAnt1()->getId()));
				printClause(getNode(n->getAnt2()->getId()));
				opensmt_error_();
			}
			for(size_t i=0;i<n->getClauseSize();i++)
				if(n->getClause()[i]!=v[i])
				{
					cerr << "Clause : "; printClause(n); cerr << " does not correctly derive from antecedents " << endl;
					printClause(getNode(n->getAnt1()->getId()));
					printClause(getNode(n->getAnt2()->getId()));
					opensmt_error_();
				}
			delete(v_);
			// Checks whether clause is tautological
			vector<Lit>& cl = n->getClause();
			for(unsigned u = 0; u < cl.size()-1; u ++)
				if(var(cl[u])==var(cl[u+1]))
				{
					cerr << "Clause : "; printClause(n); cerr << " is tautological " << endl;
				}
			// Checks whether both antecedents have the pivot
			short f1 = n->getAnt1()->hasOccurrenceBin(n->getPivot());
			short f2 = n->getAnt2()->hasOccurrenceBin(n->getPivot());
			assert( f1 != -1 ); assert( f2 != -1 ); assert( f1 != f2 );
		}
	}
	// Check that every resolvent has this node as its antecedent
	set<clauseid_t>& resolvents = n->getResolvents();
	for(set<clauseid_t>::iterator it = resolvents.begin(); it!=resolvents.end(); it++)
	{
		assert((*it)<getGraphSize());
		ProofNode* res = getNode((*it));
		if(res==NULL) {
			cerr << "Node " << n->getId() << " has resolvent " << (*it) << " null" << endl;
			opensmt_error_();
		}
		else
			assert(res->getAnt1() == n || res->getAnt2() == n);
	}
}

void ProofGraph::checkProof( bool check_clauses )
{
	if( verbose() ) cerr << "# Checking proof" << endl;

	// Visit top down
	std::deque<clauseid_t> q;
	std::vector<unsigned>* visit_level_ = new vector<unsigned>(getGraphSize());
	std::vector<unsigned>& visit_level = *visit_level_;
	q.assign(leaves_ids.begin(),leaves_ids.end());
	do
	{
		clauseid_t id=q.front();
		ProofNode* n=getNode(id);
		assert(n);
		q.pop_front();
		if(!isSetVisited2(id))
		{
			setVisited2(id);
			// Leaves are seen only once
			if(n->isLeaf())
			{
				visit_level[id] = 1;
				for(set<clauseid_t>::iterator it = n->getResolvents().begin(); it != n->getResolvents().end(); it++ ) q.push_back(*it);
			}
		}
		else
		{
			assert(! n->isLeaf() );
			assert(visit_level[id] == 0);
			// Inner should be seen twice
			for(set<clauseid_t>::iterator it = n->getResolvents().begin(); it != n->getResolvents().end(); it++ )
				{ assert(visit_level[*it] == 0); q.push_back(*it); }

			clauseid_t id1 = n->getAnt1()->getId();
			clauseid_t id2 = n->getAnt2()->getId();
			assert(visit_level[id1] > 0);
			assert(visit_level[id2] > 0);
			visit_level[id] = visit_level[id1] > visit_level[id2] ? visit_level[id1] + 1 : visit_level[id2] + 1;
		}
	}
	while(!q.empty());
	delete(visit_level_);

	// Visit bottom up
	q.push_back(getRoot()->getId());
	do
	{
		clauseid_t id = q.back();
		ProofNode* node = getNode(id);
		assert(node);
		q.pop_back();

		if(!node->isLeaf())
		{
			clauseid_t id1 = node->getAnt1()->getId();
			clauseid_t id2 = node->getAnt2()->getId();
			assert(node->getAnt1() != node->getAnt2());
			// Enqueue antecedents the first time the node is seen
			if(!isSetVisited1(id)) { q.push_back(id1); q.push_back(id2); }
			if(check_clauses) checkClause(id);
		}
		setVisited1(node->getId());
	}
	while(!q.empty());

	// Ensure that the same nodes have been visited top-down and bottom-up
	for(unsigned u = 0; u < getGraphSize(); u ++)
	{
		if( isSetVisited1(u) && !isSetVisited2(u)) {
			cerr << "Node " << u << " is unreachable going top-down" << endl; opensmt_error_();}
		if( !isSetVisited1(u) && isSetVisited2(u)) {
			cerr << "Node " << u << " is unreachable going bottom-up" << endl; opensmt_error_();}
	}

	// Ensure that there are no useless leaves
	for(set<clauseid_t>::iterator it = leaves_ids.begin(); it != leaves_ids.end(); it++)
	{
		if(!isSetVisited1(*it)) { cerr << "Detached leaf" << (*it) << endl; opensmt_error_();}
	}

	resetVisited1();
	resetVisited2();
}

#endif
