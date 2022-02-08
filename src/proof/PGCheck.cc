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


#include "PG.h"
#include <sys/wait.h>


void ProofGraph::verifyLeavesInconsistency( )
{
	if( verbose() > 0 ) { std::cerr << "# Verifying unsatisfiability of the set of proof leaves" << std::endl; }

	std::vector<clauseid_t> proofleaves;
	clauseid_t id,id1,id2;
	std::vector<clauseid_t> q;
	ProofNode * node = NULL;
	std::vector<unsigned>* visited_count_ = new std::vector<unsigned>(getGraphSize(),0);
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
	std::ofstream dump_out( name );
	logic_.dumpHeaderToFile( dump_out );

	unsigned added = 0;
	for ( unsigned i = 0 ; i < proofleaves.size( ) ; i ++ )
	{
		if(added == 0)
		{
			dump_out << "(assert " << '\n';
			dump_out << "(and" << '\n';
			added++;
		}
		printClause( dump_out, getNode(proofleaves[ i ])->getClause());
		dump_out << '\n';
	}
	if(added > 0) dump_out << "))" << '\n';

	dump_out << "(check-sat)" << '\n';
	dump_out << "(exit)" << '\n';
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
	std::vector<Lit>& cla = getAnt1()->getClause();
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
			std::cerr << "Bad clause sorting for clause " << n->getId() << " of type " << n->getType() << '\n';
			printClause(n);
			opensmt_error_();
		}
		if(var(n->getClause()[i])==var(n->getClause()[i+1]) && sign(n->getClause()[i])==sign(n->getClause()[i+1]))
		{
			std::cerr << "Repetition of var " << var(n->getClause()[i]) << " in clause " << n->getId() << " of type " << n->getType() << '\n';
			printClause(n);
			opensmt_error_();
		}
		if(var(n->getClause()[i])==var(n->getClause()[i+1]) && sign(n->getClause()[i])!=sign(n->getClause()[i+1]))
		{
			std::cerr << "Inconsistency on var " << var(n->getClause()[i]) << " in clause " << n->getId() << " of type " << n->getType() << '\n';
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
			std::cerr << n->getId() << " is the sink but not an empty clause" << '\n';
			printClause(n);
			opensmt_error_();
		}
	}
	if(n->getClauseSize()==0)
	{
		if(n->getType()==clause_type::CLA_ORIG)
		{
			std::cerr << n->getId() << " is an empty original clause" << '\n';
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
			std::vector<Lit> v;
			mergeClauses(n->getAnt1()->getClause(),n->getAnt2()->getClause(),v,n->getPivot());
			if(v.size()!=n->getClauseSize())
			{
				std::cerr << "Clause : "; printClause(n);
				std::cerr << " does not correctly derive from antecedents " << '\n';
				printClause(getNode(n->getAnt1()->getId()));
				printClause(getNode(n->getAnt2()->getId()));
				opensmt_error_();
			}
			for(size_t i=0;i<n->getClauseSize();i++)
				if(n->getClause()[i]!=v[i])
				{
					std::cerr << "Clause : "; printClause(n);
					std::cerr << " does not correctly derive from antecedents " << '\n';
					printClause(getNode(n->getAnt1()->getId()));
					printClause(getNode(n->getAnt2()->getId()));
					opensmt_error_();
				}
			// Checks whether clause is tautological
			std::vector<Lit>& cl = n->getClause();
			for(unsigned u = 0; u < cl.size()-1; u ++)
				if(var(cl[u])==var(cl[u+1]))
				{
					std::cerr << "Clause : "; printClause(n);
					std::cerr << " is tautological " << '\n';
				}
			// Checks whether both antecedents have the pivot
			short f1 = n->getAnt1()->hasOccurrenceBin(n->getPivot());
			short f2 = n->getAnt2()->hasOccurrenceBin(n->getPivot());
			assert( f1 != -1 ); assert( f2 != -1 ); assert( f1 != f2 ); (void)f1; (void)f2;
		}
	}
	// Check that every resolvent has this node as its antecedent
	std::set<clauseid_t>& resolvents = n->getResolvents();
	for (clauseid_t id : resolvents)	{
		assert(id < getGraphSize());
		ProofNode* res = getNode(id);
		if(res==NULL) {
			std::cerr << "Node " << n->getId() << " has resolvent " << id << " null" << '\n';
			opensmt_error_();
		}
		else
			assert(res->getAnt1() == n || res->getAnt2() == n);
	}
}

void ProofGraph::checkProof( bool check_clauses )
{
	if (verbose()) {
		std::cerr << "# Checking proof" << '\n';
	}

	// Visit top down
	std::deque<clauseid_t> q;
	std::vector<unsigned> visit_level(getGraphSize());
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
				for (clauseid_t resolvent_id : n->getResolvents()) {
					q.push_back(resolvent_id);
				}
			}
		}
		else
		{
			assert(! n->isLeaf() );
			assert(visit_level[id] == 0);
			// Inner should be seen twice
			for (clauseid_t resolvent_id : n->getResolvents())
				{ assert(visit_level[resolvent_id] == 0); q.push_back(resolvent_id); }

			clauseid_t id1 = n->getAnt1()->getId();
			clauseid_t id2 = n->getAnt2()->getId();
			assert(visit_level[id1] > 0);
			assert(visit_level[id2] > 0);
			visit_level[id] = visit_level[id1] > visit_level[id2] ? visit_level[id1] + 1 : visit_level[id2] + 1;
		}
	}
	while(!q.empty());

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
			std::cerr << "Node " << u << " is unreachable going top-down" << '\n'; opensmt_error_();}
		if( !isSetVisited1(u) && isSetVisited2(u)) {
			std::cerr << "Node " << u << " is unreachable going bottom-up" << '\n'; opensmt_error_();}
	}

	// Ensure that there are no useless leaves
	for (clauseid_t leave_id : leaves_ids) {
		if (not isSetVisited1(leave_id)) { std::cerr << "Detached leaf" << leave_id << '\n'; opensmt_error_();}
	}

	resetVisited1();
	resetVisited2();
}

