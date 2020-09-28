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
#include "CoreSMTSolver.h"

// Prints resolution proof graph to a dot file,
// with proper colors
void ProofGraph::printProofAsDotty(std::ostream & out, ipartitions_t A_mask) {
    // Visited nodes vector
    std::vector<bool> visited_dotty(getGraphSize(), false);
    // Visit proof graph from sink via DFS
    std::vector<ProofNode *> q;
    q.push_back(getRoot());

    out << "digraph proof {" << endl;

    while (!q.empty()) {
        ProofNode * node = q.back();
        // Remove node
        q.pop_back();
        // Node not yet visited
        if (!visited_dotty.at(node->getId())) {
            //Clean
            //clauseSort(node->clause);
            // Print node
            string typ;
            string color = "";
            switch (node->getType()) {
                case clause_type::CLA_ORIG:
                    typ = "cls_";
                    out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() << "  :  ";
                    printClause(node, out);
                    if (produceInterpolants() && node->getPartialInterpolant() != PTRef_Undef) {
                        // FIXME out << "\\\\n" << node->getPartialInterpolant( );
                        if (produceInterpolants()) {
                            icolor_t col = getClauseColor(node->getInterpPartitionMask(), A_mask);
                            if (col == I_A) out << "\", color=\"lightblue\",";
                            if (col == I_B) out << "\", color=\"red\",";
                            if (col == I_AB) out << "\", color=\"violet\",";
                        }
                    } else {
                        out << "\", color=\"lightblue\",";
                    }
                    out << " fontcolor=\"black\", style=\"filled\"]" << endl;
                    break;
                case clause_type::CLA_THEORY:
                    typ = "the_";
                    out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() << "  :  ";
                    if (!node->getClause().empty()) { printClause(node, out); }
                    else out << "+"; // learnt clause
                    if (produceInterpolants() && node->getPartialInterpolant() != PTRef_Undef) {
                        //FIXME out << "\\\\n" << node->getPartialInterpolant( );
                    }
                    out << "\", color=\"grey\"";
                    out << ", style=\"filled\"]" << endl;
                    break;
                case clause_type::CLA_LEARNT:
                    typ = "lea_";
                    out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() << "  :  ";
                    if (!node->getClause().empty()) { printClause(node, out); }
                    else out << "+"; // learnt clause
                    if (produceInterpolants() && node->getPartialInterpolant() != PTRef_Undef) {
                        //FIXME out << "\\\\n" << node->getPartialInterpolant( );
                    }
                    out << "\", color=\"orange\"";
                    out << ", style=\"filled\"]" << endl;
                    break;
                case clause_type::CLA_DERIVED:
                    typ = "der_";
                    out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() << "  :  ";
                    if (!node->getClause().empty()) { printClause(node, out); }
                    else out << "+"; // internal derived clause
                    if (produceInterpolants() && node->getPartialInterpolant() != PTRef_Undef) {
                        //FIXME out << "\\\\n" << node->getPartialInterpolant( );
                    }
                    out << "\", color=\"green\"";
                    out << ", style=\"filled\"]" << endl;
                    break;
                case clause_type::CLA_ASSUMPTION:
                    typ = "ass_";
                    out << typ << node->getId() << "[shape=plaintext, label=\"c" << node->getId() << "  :  ";
                    assert(!node->getClause().empty());
                    printClause(node, out);
                    out << "\", color=\"yellow\"";
                    out << ", style=\"filled\"]" << endl;
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
    out << "}" << endl;
}

void ProofGraph::printClause(ProofNode* n)
{
	assert(n);
	vector<Lit>& cl=n->getClause();
	cerr << n->getId();
	if(!n->isLeaf()) cerr << "(" << n->getAnt1()->getId() << "," << n->getAnt2()->getId() << ")";
	cerr << ": ";
	for(size_t k=0;k<cl.size();k++)
	{
		if(sign(cl[k])) cerr << "-";
		cerr << var(cl[k]) << " ";
	}
	cerr << endl;
}

void ProofGraph::printClause(ProofNode* n, ostream & os)
{
	assert(n);
	vector<Lit>& cl=n->getClause();
	for(size_t k=0;k<cl.size();k++)
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
        char* term_name;
        thandler->getVarName(v, &term_name);
        out << (sign(c[i])?"(not ":"") << term_name << (sign(c[i])?") ":" ");
        free(term_name);
    }
    if ( c.size( ) > 1 ) out << ")";
}

void ProofGraph::printProofNode(clauseid_t vid)
{
	ProofNode* v=getNode(vid);
	if(v==NULL)
	{
		cerr << vid << " removed"<< endl<<endl;
		return;
	}
	cerr << "Node id: " << v->getId() << "   Type: " << v->getType();
	if(v->getAnt1()!=NULL && v->getAnt2()!=NULL)
	{
		cerr << "   Parents: " << v->getAnt1()->getId() << " " << v->getAnt2()->getId() << "   Pivot: " << v->getPivot();
	}
	cerr << "   Clause: ";
	for(size_t i=0;i<v->getClauseSize();i++)
	{
		if(sign(v->getClause()[i])) cerr << "~";
		//FIXME cerr << thandler.varToEnode( var(v->getClause()[i]) ) << " ";
	}
	cerr << endl;

}

void ProofGraph::printRuleApplicationStatus()
{
	cerr << "# Rules application status " << endl;
	cerr << "# A1:           " << A1 << endl;
	cerr << "# A1prime:      " << A1prime << endl;
	cerr << "# A1B:          " << A1B << endl;
	cerr << "# A2:           " << A2 << endl;
	cerr << "# A2B:          " << A2B << endl;
	cerr << "# A2U:          " << A2U << endl;
	cerr << "# B1:           " << B1 << endl;
	cerr << "# B2prime:      " << B2prime << endl;
	cerr << "# B2:           " << B2 << endl;
	cerr << "# B3:           " << B3 << endl;
	cerr << "# duplications: " << duplications << endl;
	cerr << "# swap_ties:    " << swap_ties << endl;
}


