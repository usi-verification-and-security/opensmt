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

std::unique_ptr<std::map<Var, icolor_t>> ProofGraph::computePSFunction(const ipartitions_t & A_mask) {

    auto labels = std::make_unique<std::map<Var, icolor_t>>();

    std::map<Var, int> occ_a, occ_b;

    for (auto leafId : leaves_ids) {
        ProofNode * n = getNode(leafId);
        assert(n and n->isLeaf());
        if (n->getType() != clause_type::CLA_ORIG) {
            continue;
        }
        icolor_t col = getClauseColor(n->getClauseRef(), A_mask);
        for (Lit l : n->getClause()) {
            Var v = var(l);
            icolor_t vclass = interpolationInfo.getVarClass(v);
            if (vclass != icolor_t::I_AB) continue;
            if (col == icolor_t::I_A) {
                ++occ_a[v];
                if (occ_b.find(v) == occ_b.end()) {
                    occ_b[v] = 0;
                }
            } else if (col == icolor_t::I_B) {
                ++occ_b[v];
                if (occ_a.find(v) == occ_a.end())
                    occ_a[v] = 0;
            }
        }
    }
    assert(occ_a.size() == occ_b.size());
    for (auto const & entry : occ_a) {
        Var v = entry.first;
        int qtta = entry.second;
        int qttb = occ_b.find(v)->second;
        labels->insert({v, qtta > qttb ? icolor_t::I_A : icolor_t::I_B});
    }
    return labels;
}
