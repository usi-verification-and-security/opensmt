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

#include "OsmtInternalException.h"

#include <cmath>
#include <deque>

short ProofNode::hasOccurrenceBin(Var v) {
    std::vector<Lit>& cla = getClause();
    int first=0;
    int last=cla.size()-1;

    while (first <= last) {
        int mid = (first + last) / 2;
        Lit l = cla[mid]; Var w = var(l);
        if (v > w) first = mid + 1;
        else if (v < w) last = mid - 1;
        else if( v == w ) return (sign(l) == false) ? 0 : 1;
    }
    return -1;
}

// Calculate graph info
// Assume proof filled
void ProofGraph::getGraphInfo()
{
    //Visit graph from sink keeping track of edges and nodes
    std::deque<ProofNode*> q;
    ProofNode* n;

    av_cla_size=0;
    max_cla_size=0;
    var_cla_size=0;
    num_nodes=0;
    num_edges=0;
    num_unary=0;
    num_leaves=0;
    proof_variables.clear();

    q.push_back(getRoot());
    do
    {
        n=q.front();
        q.pop_front();

        // Node not visited yet
        if (!isSetVisited1(n->getId()))
        {
            if (!n->isLeaf())
            {
                q.push_back(n->getAnt1());
                num_edges++;
                q.push_back(n->getAnt2());
                num_edges++;
                proof_variables.insert(n->getPivot());
            }
            else
            {
                assert(isLeafClauseType(n->getType()));
                num_leaves++;
            }

            //Mark node as visited
            setVisited1(n->getId());
            num_nodes++;
            av_cla_size+=n->getClauseSize();
            if (n->getClauseSize() > (size_t)max_cla_size) max_cla_size=n->getClauseSize();
            if (n->getClauseSize()==1) num_unary++;
        }
    }
    while(!q.empty());

    av_cla_size /= num_nodes;
    // Calculate sample variance for num resolvents and clause size
    for (size_t i=0;i<getGraphSize();i++)
        if (getNode(i)!=NULL)
        {
            var_cla_size+=pow(getNode(i)->getClauseSize()-av_cla_size,2);
        }
    var_cla_size/=(num_nodes-1);
    resetVisited1();
}

std::vector<clauseid_t> ProofGraph::topolSortingTopDown() const {
    std::vector<clauseid_t> DFS;
    std::deque<clauseid_t> q;
    DFS.reserve(getGraphSize());
    // Enqueue leaves first
    q.assign(leaves_ids.begin(),leaves_ids.end());
    do {
        clauseid_t id = q.front();
        q.pop_front();
        ProofNode * n = getNode(id);
        assert(n);
        if (not isSetVisited1(id)) {
            // Process node if both antecedents visited
            if ((not n->getAnt1() or isSetVisited1(n->getAnt1()->getId())) and
                (not n->getAnt2() or isSetVisited1(n->getAnt2()->getId()))) {
                for (clauseid_t resolvent_id: n->getResolvents()) {
                    if (getNode(resolvent_id)) q.push_back(resolvent_id);
                }
                setVisited1(id);
                DFS.push_back(id);
            }
        }
    }
    while(not q.empty());
    resetVisited1();
    return DFS;
}

std::vector<clauseid_t> ProofGraph::topolSortingBotUp() const {
    std::vector<clauseid_t> DFS;
    DFS.reserve(getGraphSize());
    std::vector<clauseid_t> q;
    std::vector<unsigned> visited_count(getGraphSize(),0);
    q.push_back(getRoot()->getId());
    do {
        clauseid_t id = q.back();
        ProofNode * node = getNode(id);
        assert(node);
        visited_count[id]++;
        q.pop_back();

        // All resolvents have been visited
        if (visited_count[id] == node->getNumResolvents() or id == getRoot()->getId()) {
            if (not node->isLeaf()) {
                clauseid_t id1 = node->getAnt1()->getId();
                clauseid_t id2 = node->getAnt2()->getId();
                assert(visited_count[id1] < node->getAnt1()->getNumResolvents());
                assert(visited_count[id2] < node->getAnt2()->getNumResolvents());
                q.push_back(id1);
                q.push_back(id2);
            }
            DFS.push_back(id);
        }
    } while (not q.empty());
    return DFS;
}

/*
 * Given two clauses A and B, and a pivot variable, computes the resolvent clause after resolution.
 *
 * PRECONDITION: Literals in the input clauses must be sorted and the clauses must contain the pivot variable.
 * POSTCONDITION: Literals in the resolvent clause are sorted and the clause does not contain the pivot.
 */
bool ProofGraph::mergeClauses(std::vector<Lit> const & A, std::vector<Lit> const & B, std::vector<Lit>& resolv, Var pivot)
{
    assert(std::is_sorted(A.begin(), A.end()));
    assert(std::is_sorted(B.begin(), B.end()));
    assert(std::find_if(A.begin(), A.end(), [pivot](Lit l) { return var(l) == pivot; }) != A.end());
    assert(std::find_if(B.begin(), B.end(), [pivot](Lit l) { return var(l) == pivot; }) != B.end());
    const std::size_t Asize = A.size();
    const std::size_t Bsize = B.size();
    if (resolv.size() < Asize + Bsize - 2) {
        resolv.resize(Asize + Bsize - 2);
    }
    assert(resolv.size() >= Asize + Bsize - 2);

    std::size_t i = 0;
    std::size_t j = 0;
    std::size_t res = 0;

    auto addIfNotPivot = [&resolv, &res, pivot](Lit l) {
        if (var(l) != pivot) {
            assert(res == 0 or resolv[res - 1] != l);
            resolv[res++] = l;
        }
    };

    while (i < Asize and j < Bsize) {
        if (A[i] <= B[j]) {
            if (A[i] == B[j]) { ++j; }
            addIfNotPivot(A[i]);
            ++i;
        } else {
            assert(B[j] < A[i]);
            addIfNotPivot(B[j]);
            ++j;
        }
    }

    while (i < Asize) {
        addIfNotPivot(A[i]);
        ++i;
    }

    while (j < Bsize) {
        addIfNotPivot(B[j]);
        ++j;
    }
    assert(resolv.size() >= res);
    resolv.resize(res);
    assert(std::is_sorted(resolv.begin(), resolv.end()));
    assert(std::find_if(resolv.begin(), resolv.end(), [pivot](Lit l) { return var(l) == pivot; }) == resolv.end());
    return true;
}



void ProofGraph::analyzeProofLocality(const ipartitions_t & A_mask)
{
	std::cerr << "# Analyzing proof locality" << '\n';
	unsigned num_A_local = 0, num_B_local = 0, num_AB_common = 0, num_AB_mixed = 0, num_sym_elim = 0;
	//Visit graph from sink keeping track of edges and nodes
	std::deque<ProofNode*> q;
	ProofNode* n;
	std::deque<bool> visit(getGraphSize(),false);

	q.push_back(getRoot());
	do
	{
		n=q.front();
		q.pop_front();

		//Node not visited yet
		if(!visit[n->getId()])
		{
			if(!n->isLeaf())
			{
				q.push_back(n->getAnt1());
				q.push_back(n->getAnt2());

				// Determine if resolution step is local, that is
				// 1) all variables are A or AB
				// 2) all variables are B or AB
				bool clause_has_A_local = false;
				bool clause_has_B_local = false;
				// Determine if resolution step is symbol-eliminating, that is
				// 1) At least an antecedent has local variables
				// 2) The resolvent has only AB variables
				bool resolvent_is_clean = false;
				std::vector<Lit>& c1 = n->getAnt1()->getClause();
				std::vector<Lit>& c2 = n->getAnt2()->getClause();
				std::vector<Lit>& c = n->getClause();

				for(unsigned i = 0; i < c1.size(); i++)
				{
					icolor_t v_class = getVarClass( var(c1[i]), A_mask );
					if( v_class == icolor_t::I_A ){ clause_has_A_local = true; }
					else if( v_class == icolor_t::I_B ){ clause_has_B_local = true; }
					else if( v_class == icolor_t::I_AB ){}
                    else throw OsmtInternalException();
				}
				for(unsigned i = 0; i < c2.size(); i++)
				{
					icolor_t v_class = getVarClass( var(c2[i]), A_mask );
					if( v_class == icolor_t::I_A ){ clause_has_A_local = true; }
					else if( v_class == icolor_t::I_B ){ clause_has_B_local = true; }
					else if( v_class == icolor_t::I_AB ){}
                    else throw OsmtInternalException();
				}
				for(unsigned i = 0; i < c.size(); i++)
				{
					icolor_t v_class = getVarClass( var(c[i]), A_mask );
					if( v_class == icolor_t::I_A ){ clause_has_A_local = true; resolvent_is_clean = false; }
					else if( v_class == icolor_t::I_B ){ clause_has_B_local = true; resolvent_is_clean = false; }
					else if( v_class == icolor_t::I_AB ){}
                    else throw OsmtInternalException();
				}
				if (!clause_has_A_local && !clause_has_B_local)     num_AB_common++;
				else if (clause_has_A_local && !clause_has_B_local) num_A_local++;
				else if (!clause_has_A_local && clause_has_B_local) num_B_local++;
				else if (clause_has_A_local && clause_has_B_local)  num_AB_mixed++;
				if((clause_has_A_local || clause_has_B_local) && resolvent_is_clean) num_sym_elim++;
			}
			else
			{
				// Determine if leaf is symbol-eliminating, that is
				// 1) The leaf has only AB variables
				bool clause_has_A_local = false;
				bool clause_has_B_local = false;
				std::vector<Lit>& c = n->getClause();

				for(unsigned i = 0; i < c.size(); i++)
				{
					icolor_t v_class = getVarClass( var(c[i]), A_mask );
					if( v_class == icolor_t::I_A ){ clause_has_A_local = true; }
					else if( v_class == icolor_t::I_B ){ clause_has_B_local = true; }
					else if( v_class == icolor_t::I_AB ){}
					else throw OsmtInternalException();
				}
				if (!clause_has_A_local && !clause_has_B_local) num_sym_elim++;
			}
			//Mark node as visited
			visit[n->getId()]=true;
		}
	}
	while(!q.empty());
	std::cerr << "# AB common steps  :" << num_AB_common << '\n';
	std::cerr << "# A local steps    :" << num_A_local << '\n';
	std::cerr << "# B local steps    :" << num_B_local << '\n';
	std::cerr << "# A B mixed steps  :" << num_AB_mixed << '\n';
	std::cerr << "# Sym elim steps   :" << num_sym_elim << '\n';
}
