/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "ClausePrinter.h"
#include "Proof.h"

#include "FSBVTheory.h"

void ModelCounter::count(vec<PTRef> const & terms) const {
    // print all clauses
    auto & theory = dynamic_cast<FSBVTheory&>(theory_handler.getTheory());

    ofstream out;
    out.open(config.get_counting_output_file());

    unsigned int numOfDisappearedAtoms = 0;

    // Include the vars that need to be counted but were optimised away in simplification to total var count
    for (PTRef countTerm : terms) {
        BitWidth_t bitWidth = theory.getLogic().getRetSortBitWidth(countTerm);
        if (bvTermToVars.find(countTerm) != bvTermToVars.end()) {
            auto const & varSet = bvTermToVars.at(countTerm);
            assert(varSet.size() <= bitWidth);
            numOfDisappearedAtoms += (bitWidth - varSet.size());
        } else {
            numOfDisappearedAtoms += bitWidth;
        }
    }

    std::string bbVarString("c ind ");

    for (PTRef tr : terms) {
        for (auto v : bvTermToVars.at(tr)) {
            bbVarString += std::to_string(v+1) + " ";
        }
    }
    // Add phony vars for correct counting also to ind
    for (unsigned int i = 0; i < numOfDisappearedAtoms; i++) {
        bbVarString += std::to_string(nVars()+i+1) + " ";
    }

    out << bbVarString + "0\n";

    out << "p cnf " + std::to_string(nVars() + numOfDisappearedAtoms) + " " + std::to_string(nClauses()) << std::endl;
    for (vec<Lit> const & smtClause : clauses) {
        for (Lit l: smtClause) {
            Var v = var(l);
            out << (sign(l) ? -(v + 1) : (v + 1)) << " ";
        }
        out << "0" << std::endl;
    }
}

void ModelCounter::addVar(Var v) {
    if (not vars.has(v)) {
        vars.insert(v, true);
        ++ numberOfVarsSeen;
    }
}

bool ModelCounter::addOriginalSMTClause(vec<Lit> const & smtClause, opensmt::pair<CRef, CRef> &) {
    auto & theory = dynamic_cast<FSBVTheory&>(theory_handler.getTheory());
    auto & bbTermToBVTerm = theory.getBBTermToBVTerm();
    for (Lit l : smtClause) {
        Var v = var(l);
        if (not vars.has(v)) {
            // A new variable
            vars.insert(v, true);
            numberOfVarsSeen++;

            PTRef bbTerm = theory_handler.varToTerm(v);
            if (bbTermToBVTerm.find(bbTerm) != bbTermToBVTerm.end()) {
                // The variable originates from bit-blasted gate
                // Update the bits of the gate
                PTRef bvTerm = bbTermToBVTerm.at(bbTerm);
                bvTermToVars[bvTerm].insert(v);
            }
        }
    }
    vec<Lit> outClause;
    smtClause.copyTo(outClause);
    clauses.push_back(std::move(outClause));
    return true;
}
