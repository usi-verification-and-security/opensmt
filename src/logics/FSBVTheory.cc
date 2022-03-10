/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "FSBVTheory.h"
#include "OsmtInternalException.h"
#include "TreeOps.h"
#include "BitBlasterRewriter.h"

static SolverDescr descr_bb_solver("BitBlaster", "BitBlaster for counting models?");

bool FSBVTheory::simplify(vec<PFRef> const & formulas, PartitionManager &, int curr) {
    if (keepPartitions()) {
        throw OsmtInternalException("Mode not supported for QF_BV yet");
    } else {

        PTRef coll_f = getCollateFunction(formulas, curr);
        PTRef trans = getLogic().learnEqTransitivity(coll_f);
        coll_f = getLogic().mkAnd(coll_f, trans);
        auto subs_res = computeSubstitutions(coll_f);
        PTRef fla = flaFromSubstitutionResult(subs_res);

        vec<PTRef> bvFormulas;
        topLevelConjuncts(logic, fla, bvFormulas);

        BitBlasterRewriter bitBlasterRewriter(logic);
        PTRef out = bitBlasterRewriter.rewrite(logic.mkAnd(bvFormulas));
        bbTermToBVTerm = bitBlasterRewriter.getBitBlastedTermToBitVectorTermMap();

        subs_res = computeSubstitutions(out);
        fla = flaFromSubstitutionResult(subs_res);
        pfstore[formulas[curr]].root = fla;
        return false;
    }
}