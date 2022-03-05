/*
 *  Copyright (c) 2013, Simone Fulvio Rollini <simone.rollini@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "PG.h"

// Prints resolution proof graph to a dot file,
// with proper colors
void ProofGraph::printProofAsDotty(std::ostream & out) {
    // Visited nodes vector
    std::vector<bool> visited_dotty(getGraphSize(), false);
    // Visit proof graph from sink via DFS
    std::vector<ProofNode *> q;
    q.push_back(getRoot());

    out << "digraph proof {" << '\n';

    while (!q.empty()) {
        ProofNode * node = q.back();
        // Remove node
        q.pop_back();
        // Node not yet visited
        if (!visited_dotty.at(node->getId())) {
            //Clean
            //clauseSort(node->clause);
            // Print node
            std::string typ;
            std::string color = "";
            switch (node->getType()) {
                case clause_type::CLA_ORIG:
                    typ = "cls_";
                    out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() << "  :  ";
                    printClause(node, out);
                    out << "\", color=\"lightblue\",";
                    out << " fontcolor=\"black\", style=\"filled\"]" << '\n';
                    break;
                case clause_type::CLA_THEORY:
                    typ = "the_";
                    out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() << "  :  ";
                    if (!node->getClause().empty()) { printClause(node, out); }
                    else out << "+"; // learnt clause
                    out << "\", color=\"grey\"";
                    out << ", style=\"filled\"]" << '\n';
                    break;
                case clause_type::CLA_LEARNT:
                    typ = "lea_";
                    out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() << "  :  ";
                    if (!node->getClause().empty()) { printClause(node, out); }
                    else out << "+"; // learnt clause
                    out << "\", color=\"orange\"";
                    out << ", style=\"filled\"]" << '\n';
                    break;
                case clause_type::CLA_DERIVED:
                    typ = "der_";
                    out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() << "  :  ";
                    if (!node->getClause().empty()) { printClause(node, out); }
                    else out << "+"; // internal derived clause
                    out << "\", color=\"green\"";
                    out << ", style=\"filled\"]" << '\n';
                    break;
                case clause_type::CLA_ASSUMPTION:
                    typ = "ass_";
                    out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() << "  :  ";
                    assert(!node->getClause().empty());
                    printClause(node, out);
                    out << "\", color=\"yellow\"";
                    out << ", style=\"filled\"]" << '\n';
                    break;
                case clause_type::CLA_SPLIT:
                    typ = "spl_";
                    out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() << "  :  ";
                    assert(not node->getClause().empty());
                    printClause(node, out);
                    out << "\", color=\"purple\"";
                    out << ", style=\"filled\"]" << '\n';
                    break;
                default:
                    assert(false);
                    typ = "";
                    break;
            }

            // Print edges from parents (if existing)
            auto addEdgeToParent = [&out, &typ](const ProofNode & parent, const ProofNode & child) {
                std::string t1;
                switch (parent.getType()) {
                    case clause_type::CLA_ORIG:
                        t1 = "cls_";
                        break;
                    case clause_type::CLA_THEORY:
                        t1 = "the_";
                        break;
                    case clause_type::CLA_LEARNT:
                        t1 = "lea_";
                        break;
                    case clause_type::CLA_DERIVED:
                        t1 = "der_";
                        break;
                    case clause_type::CLA_ASSUMPTION:
                        t1 = "ass_";
                        break;
                    case clause_type::CLA_SPLIT:
                        t1 = "spl_";
                        break;
                    default:
                        assert(false);
                        t1 = "";
                        break;
                }
                out << t1 << parent.getId() << " -> " << typ << child.getId() << '\n';
            };
            ProofNode * r1 = node->getAnt1();
            ProofNode * r2 = node->getAnt2();
            if (r1 != nullptr) {
                addEdgeToParent(*r1, *node);
                // Enqueue the parent
                q.push_back(r1);
            }
            if (r2 != nullptr) {
                addEdgeToParent(*r2, *node);
                // Enqueue the parent
                q.push_back(r2);
            }
            //Mark node as visited
            visited_dotty[node->getId()] = true;
        }
    }
    out << "}" << '\n';
}

void ProofGraph::printClause(ProofNode* n)
{
	assert(n);
	std::vector<Lit>& cl=n->getClause();
	std::cerr << n->getId();
	if(!n->isLeaf()) std::cerr << "(" << n->getAnt1()->getId() << "," << n->getAnt2()->getId() << ")";
	std::cerr << ": ";
	for(size_t k=0;k<cl.size();k++)
	{
		if(sign(cl[k])) std::cerr << "-";
		std::cerr << var(cl[k]) << " ";
	}
	std::cerr << '\n';
}

void ProofGraph::printClause(ProofNode* n, std::ostream & os)
{
	assert(n);
	std::vector<Lit> & cl = n->getClause();
	for (size_t k = 0 ; k < cl.size(); k++)
	{
		if(sign(cl[k])) { os << "-"; }
		os << var(cl[k]) << " ";
	}
}

void ProofGraph::printClause(std::ostream & out, std::vector<Lit> const & c) {
    if ( c.size( ) == 0 ) out << "-";
    if ( c.size( ) > 1 ) out << "(or ";
    for (unsigned i = 0; i < c.size(); i++)
    {
        Var v = var(c[i]);
        if ( v <= 1 ) continue;
        out << (sign(c[i])?"(not ":"") << logic_.printTerm(termMapper.varToPTRef(v)) << (sign(c[i])?") ":" ");
    }
    if ( c.size( ) > 1 ) out << ")";
}

void ProofGraph::printProofNode(clauseid_t vid)
{
	ProofNode* v=getNode(vid);
	if(v==NULL)
	{
		std::cerr << vid << " removed"<< '\n'<<'\n';
		return;
	}
	std::cerr << "Node id: " << v->getId() << "   Type: " << v->getType();
	if(v->getAnt1()!=NULL && v->getAnt2()!=NULL)
	{
		std::cerr << "   Parents: " << v->getAnt1()->getId() << " " << v->getAnt2()->getId() << "   Pivot: " << v->getPivot();
	}
	std::cerr << "   Clause: ";
	for(size_t i=0;i<v->getClauseSize();i++)
	{
		if(sign(v->getClause()[i])) std::cerr << "~";
		//FIXME std::cerr << thandler.varToEnode( var(v->getClause()[i]) ) << " ";
	}
	std::cerr << '\n';

}

void ProofGraph::printRuleApplicationStatus()
{
	std::cerr << "# Rules application status " << '\n';
	std::cerr << "# A1:           " << A1 << '\n';
	std::cerr << "# A1prime:      " << A1prime << '\n';
	std::cerr << "# A1B:          " << A1B << '\n';
	std::cerr << "# A2:           " << A2 << '\n';
	std::cerr << "# A2B:          " << A2B << '\n';
	std::cerr << "# A2U:          " << A2U << '\n';
	std::cerr << "# B1:           " << B1 << '\n';
	std::cerr << "# B2prime:      " << B2prime << '\n';
	std::cerr << "# B2:           " << B2 << '\n';
	std::cerr << "# B3:           " << B3 << '\n';
	std::cerr << "# duplications: " << duplications << '\n';
	std::cerr << "# swap_ties:    " << swap_ties << '\n';
}


