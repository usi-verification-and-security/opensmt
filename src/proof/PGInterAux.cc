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


/************************* HELPERS ******************************/

bool ProofGraph::decideOnAlternativeInterpolation(ProofNode & n)
{
	// Get antecedents partial interpolants
	PTRef I1 = interpolationInfo.getPartialInterpolant(*n.getAnt1());
	PTRef I2 = interpolationInfo.getPartialInterpolant(*n.getAnt2());
	assert( I1 != PTRef_Undef ); assert( I2 != PTRef_Undef );
	bool I1_is_true = ( I1 == logic_.getTerm_true() );
	bool I2_is_true = ( I2 == logic_.getTerm_true() );
	bool I1_is_false = ( I1 == logic_.getTerm_false() );
	bool I2_is_false = ( I2 == logic_.getTerm_false() );
	bool I1_is_none = ( !I1_is_true && !I1_is_false );
	bool I2_is_none = ( !I2_is_true && !I2_is_false );

	// For some combinations of I1, I2, the alternative interpolant
	// has a smaller size!
	// Standard     (I1 \/ p ) /\ (I2 \/ ~p)
	// Alternative  (I1 /\ ~p) \/ (I2 /\ p)

	if(I1_is_false && I2_is_none) return true;
	if(I1_is_none && I2_is_false) return true;
	if(I1_is_false && I2_is_false) return true;
	return false;
}


icolor_t ProofGraph::getVarColor(ProofNode const & n, Var v) {
    assert(n.isLeaf());
    // In labeling, classes and colors are distinct
    icolor_t var_class = interpolationInfo.getVarClass(v);
    assert(var_class == icolor_t::I_A or var_class == icolor_t::I_B or var_class == icolor_t::I_AB);
    icolor_t var_color = var_class == icolor_t::I_B || var_class == icolor_t::I_A ? var_class
            : getSharedVarColorInNode(v, n);
    return var_color;
}

// Input: node, current interpolant partition masks for A and B
// Output: returns node pivot color as a, b or ab
// depending on the colors in the node antecedents
icolor_t ProofGraph::getPivotColor(ProofNode const & n) {
    assert(not n.isLeaf());
    Var v = n.getPivot();
	// In labeling, classes and colors are distinct
	icolor_t var_class = interpolationInfo.getVarClass(v);
    if (var_class != icolor_t::I_A and var_class != icolor_t::I_B and var_class != icolor_t::I_AB) {
        throw OsmtInternalException("Pivot " + std::to_string(v) + " has no class");
    }

	// Update AB vars color vectors from antecedents
	interpolationInfo.updateColoringfromAnts(n);

    // Determine if variable A-local, B-local or AB-common
	icolor_t var_color = var_class;
	if (var_color != icolor_t::I_A and var_color != icolor_t::I_B) {
        assert(var_class == icolor_t::I_AB);
        var_color = getSharedVarColorInNode(v, n);
        // Remove pivot from resolvent if class AB
        interpolationInfo.clearPivotColoring(n);
	}
    if (isAssumedVar(v)) { // Small hack to deal with assumption literals in proof
        return icolor_t::I_S;
    }
	return var_color;
}

namespace {
icolor_t getClass(ipartitions_t const & mask, ipartitions_t const & A_mask) {
    ipartitions_t B_mask = ~A_mask;

    // Check if belongs to A or B
    const bool in_A = ((mask & A_mask) != 0);
    const bool in_B = ((mask & B_mask) != 0);
    assert(in_A or in_B);

    icolor_t clause_color = icolor_t::I_UNDEF;
    if (in_A and not in_B) clause_color = icolor_t::I_A;
    else if (not in_A and in_B) clause_color = icolor_t::I_B;
    else if (in_A and in_B) clause_color = icolor_t::I_AB;
    else throw OsmtInternalException("No class could have been determined");

    return clause_color;
}
}

// Input: variable, current interpolant partition masks for A
// Output: returns A-local , B-local or AB-common
icolor_t ProofGraph::getVarClass(Var v, const ipartitions_t & A_mask) {
    if (this->isAssumedVar(v)) { return icolor_t::I_AB; } // MB: Does not matter for assumed literals
    const ipartitions_t & var_mask = this->getVarPartition(v);
    return getClass(var_mask, A_mask);
}

// Input: proof node, current interpolant partition masks for A
// Output: returns A, B or AB
icolor_t ProofGraph::getClauseColor(CRef clause, ipartitions_t const & A_mask) {
    auto const & clause_mask = pmanager.getClauseClassMask(clause);
    return getClass(clause_mask, A_mask);
}

std::map<Var, icolor_t>*
ProofGraph::computePSFunction(std::vector< clauseid_t >& DFSv, const ipartitions_t& A_mask)
{
	size_t proof_size = DFSv.size();

	std::map<Var, icolor_t> * labels = nullptr;
	ProofNode *n;
    theory_only.clear();
	if(needProofStatistics())
	{
		labels = new std::map<Var, icolor_t>();

		time_t after, before;
		time(&before);
		
		std::map<Var, int> occ_a, occ_b;

		for(size_t i = 0; i < proof_size; ++i)
		{
			n = getNode(DFSv[i]); assert(n);
			if(!n->isLeaf()) continue;
            if(n->getType() == clause_type::CLA_THEORY)
            {
                std::vector<Lit>& tlits = n->getClause();
                if(!tlits.empty())
                {
                    for(int i = 0; i < int(tlits.size()); ++i)
                    {
                        int v = var(tlits.at(i));
                        if(theory_only.find(v) == theory_only.end())
                            theory_only.insert(v);
                    }
                }
                continue;
            }
			if(n->getType() != clause_type::CLA_ORIG)
			{
                // FIXME: This check is outdated
                throw OsmtInternalException( "Clause is not original" );
			}

			icolor_t col = getClauseColor(n->getClauseRef(), A_mask);
			std::vector<Lit>& lits = n->getClause();
			if(!lits.empty())
			{
				for(int i = 0; i < int(lits.size()); ++i)
				{
					int v = var(lits.at(i));
                    
                    if(theory_only.find(v) != theory_only.end())
                        theory_only.erase(theory_only.find(v));

					icolor_t vclass = interpolationInfo.getVarClass(v);
					if(vclass != icolor_t::I_AB) continue;
					if(col == icolor_t::I_A)
					{
						++occ_a[v];
						if(occ_b.find(v) == occ_b.end())
							occ_b[v] = 0;
					}
					else if(col == icolor_t::I_B)
					{
						++occ_b[v];
						if(occ_a.find(v) == occ_a.end())
							occ_a[v] = 0;
					}
				}
			}
		}
		assert(occ_a.size() == occ_b.size());
		int avars, bvars, aevars, bevars;
		avars = bvars = aevars = bevars = 0;
		srand(time(nullptr));
		for(auto it = occ_a.begin(); it != occ_a.end(); ++it)
		{
			Var v = it->first;
			int qtta = it->second;
			int qttb = occ_b.find(v)->second;
			bool fa = true; //suppose label is A
			if(qtta == qttb)
			{
				//if(rand() % 2) fa = false; //random == 1, label B (breaks path-interpolation property!!!)
				fa = false;
			}
			else if(qttb > qtta) //b greater label B
				fa = false;

			if(fa)
			{
				if(qtta > qttb) ++avars; else ++aevars;
				labels->insert(std::pair<Var, icolor_t>(v, icolor_t::I_A));
			}
			else
			{
				if(qttb > qtta) ++bvars; else ++bevars;
				labels->insert(std::pair<Var, icolor_t>(v, icolor_t::I_B));
			}
		}
		///////////////////////////////////////////////////////////
		time(&after);
        if(verbose())
    		std::cout << "; Time spent computing PS labeling function: " << difftime(after, before) << "s" << '\n';
	}

	return labels;
}
