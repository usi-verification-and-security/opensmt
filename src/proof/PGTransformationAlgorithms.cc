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
#include "CoreSMTSolver.h" // TODO: MB: deal with reportf and remove this include
#include "OsmtInternalException.h"

#include <unordered_set>

//************************* RECYCLE PIVOTS AND RECYCLE UNITS ***************************

/*
 * Recycle phase of recycle pivots with intersection expects the proof is in a legal form.
 * After this phase the proof may not be in a legal form and must be reconstructed.
 */
void ProofGraph::recyclePivotsIter_RecyclePhase() {
    // Each node has associated bitvector containing the set of positive/negative pivots
    // present in all paths in its subgraph down to the root

    // Increased sets for taking into account pivots
    mpz_t incr_safe_lit_set_1;
    mpz_init(incr_safe_lit_set_1);
    mpz_t incr_safe_lit_set_2;
    mpz_init(incr_safe_lit_set_2);

    const size_t size = getGraphSize();
    auto * safe_lit_set = new mpz_t[size];

    // Allocate root bitset
    mpz_init(safe_lit_set[getRoot()->getId()]);

    //DFS vector
    std::vector<clauseid_t> DFSvec;
    topolSortingBotUp(DFSvec);

    assert(isResetVisited1());
    // To initialize pivots set to the set of the first resolvent
    for (clauseid_t id : DFSvec) {
        ProofNode * n = getNode(id);
        assert(n);

        // Remove nodes left without resolvents
        if (not isRoot(n) and n->getNumResolvents() == 0) {
            if (n->getAnt1()) { n->getAnt1()->remRes(id); }
            if (n->getAnt2()) { n->getAnt2()->remRes(id); }
            if (isSetVisited1(id)) { mpz_clear(safe_lit_set[id]); }
            removeNode(id);
        } else if (not n->isLeaf()) {
            clauseid_t id1 = n->getAnt1()->getId();
            clauseid_t id2 = n->getAnt2()->getId();
            Var piv = n->getPivot();
            int pos_piv = toInt(mkLit(piv, false));
            int neg_piv = toInt(mkLit(piv, true));

            short out = n->getAnt1()->hasOccurrenceBin(piv);
            assert(out != -1);
            // TODO guarantee positive occurrence pivot in ant1
            bool ant1_has_pos_occ_piv = (out == 0);

            assert(n->getAnt1());
            assert(n->getAnt2());
            enum class Replace : char {NO, ANT1, ANT2};
            Replace replace = Replace::NO;
            // Check whether pivot present in all subgraph paths
            if (mpz_tstbit(safe_lit_set[id], pos_piv)) {
                replace = ant1_has_pos_occ_piv ? Replace::ANT1 : Replace::ANT2;
            } else if (mpz_tstbit(safe_lit_set[id], neg_piv)) {
                replace = ant1_has_pos_occ_piv ? Replace::ANT2 : Replace::ANT1;
            }
            // A node marked to be replaced is left with the replacing
            // antecedent at ant1 and with ant2 set to NULL
            if (replace == Replace::ANT1) {
                n->getAnt2()->remRes(id);
                n->setAnt2(nullptr);
            } else if (replace == Replace::ANT2) {
                n->getAnt1()->remRes(id);
                n->setAnt1(n->getAnt2());
                n->setAnt2(nullptr);
            }

            // Update antecedents pivots sets
            // If we are replacing, just copy the pivot set
            // Otherwise, intersect the antecedent's set with current one enriched with pivot (or just initialize if not visited yet)
            auto updateSet = [this, &safe_lit_set](clauseid_t id, mpz_t const &other) {
                if (not isSetVisited1(id)) {
                    mpz_init(safe_lit_set[id]);
                    setVisited1(id);
                    mpz_set(safe_lit_set[id], other);
                } else
                    mpz_and(safe_lit_set[id], safe_lit_set[id], other);
            };
            switch (replace) {
                case Replace::NO:
                {
                    // Set pivot bit for propagation
                    mpz_set(incr_safe_lit_set_1, safe_lit_set[id]);
                    mpz_set(incr_safe_lit_set_2, safe_lit_set[id]);

                    mpz_setbit(incr_safe_lit_set_1, ant1_has_pos_occ_piv ? pos_piv : neg_piv);
                    mpz_setbit(incr_safe_lit_set_2, ant1_has_pos_occ_piv ? neg_piv : pos_piv);

                    updateSet(id1, incr_safe_lit_set_1);
                    updateSet(id2, incr_safe_lit_set_2);
                    break;
                }
                case Replace::ANT1:
                    updateSet(id1, safe_lit_set[id]);
                    break;
                case Replace::ANT2:
                    updateSet(id2, safe_lit_set[id]);
                    break;
                default:
                    assert(false);
            }
            // NOTE important, free memory for node id
            mpz_clear(safe_lit_set[id]);
        } else {
            assert(n->isLeaf());
            // NOTE important, free memory for node id
            mpz_clear(safe_lit_set[id]);
        }
    }

    delete[] safe_lit_set;
    mpz_clear(incr_safe_lit_set_1);
    mpz_clear(incr_safe_lit_set_2);
    resetVisited1();
}

double ProofGraph::recyclePivotsIter() {
    if (verbose() > 1) { std::cerr << "; Recycle pivots plus restructuring begin" << std::endl; }
    if (verbose() > 1) {
        uint64_t mem_used = memUsed();
        reportf("; Memory used before recycling: %.3f MB\n", mem_used == 0 ? 0 : mem_used / 1048576.0);
    }
    double initTime = cpuTime();

    recyclePivotsIter_RecyclePhase();

    if (verbose() > 1) { std::cerr << "; Recycling end, restructuring begin" << std::endl; }
    if (verbose() > 1) {
        uint64_t mem_used = memUsed();
        reportf("; Memory used after recycling, before restructuring: %.3f MB\n",
            mem_used == 0 ? 0 : mem_used / 1048576.0);
    }

    auto hasBeenReplaced = [](ProofNode * node) { return node->getAnt1() and not node->getAnt2(); };
    // Restructuring, from leaves to root
    assert(isResetVisited2());
    std::deque<clauseid_t> q;
    q.assign(leaves_ids.begin(), leaves_ids.end());
    do {
        clauseid_t id = q.front();
        assert(id < getGraphSize());
        ProofNode * n = getNode(id);
        q.pop_front();
        if (not n or isSetVisited2(id)) { continue; }
        if (n->getAnt1() and not isSetVisited2(n->getAnt1()->getId())) { continue; }
        if (n->getAnt2() and not isSetVisited2(n->getAnt2()->getId())) { continue; }
        // Mark node as visited if both antecedents visited
        setVisited2(id);
        //Non leaf node
        if (n->getAnt1() or n->getAnt2()) {
            assert(n->getAnt1() or not n->getAnt2());
            // If replaced assign children to replacing node and remove
            if (hasBeenReplaced(n)) {
                ProofNode * replacing = n->getAnt1();
                auto const & resolvents = n->getResolvents();
                for (clauseid_t resId : resolvents) {
                    assert(resId < getGraphSize());
                    ProofNode * res = getNode(resId);
                    assert(res);
                    assert(n == res->getAnt1() or n == res->getAnt2());
                    if (res->getAnt1() == n) { res->setAnt1(replacing); }
                    else if (res->getAnt2() == n) { res->setAnt2(replacing); }
                    else { throw OsmtInternalException("Invalid proof structure " + std::string(__FILE__) + ", " + std::to_string(__LINE__)); }
                    replacing->addRes(resId);
                    assert(not isSetVisited2(resId));
                    q.push_back(resId);
                }
                replacing->remRes(id);
                assert(n == getNode(id));
                removeNode(id);
                assert(replacing->getNumResolvents() > 0);
                // NOTE extra check
                if (proofCheck() > 1) { checkClause(replacing->getId()); }
            } else { // node stays
                assert(n->getAnt1() and n->getAnt2());
                assert((n->getAnt1()->getAnt1() and n->getAnt1()->getAnt2())
                       or (not n->getAnt1()->getAnt1() and not n->getAnt1()->getAnt2()));
                assert((n->getAnt2()->getAnt1() and n->getAnt2()->getAnt2())
                       or (not n->getAnt2()->getAnt1() and not n->getAnt2()->getAnt2()));

                //Look for pivot in antecedents
                bool piv_in_ant1 = false, piv_in_ant2 = false;
                short f1 = n->getAnt1()->hasOccurrenceBin(n->getPivot());
                if (f1 != -1) { piv_in_ant1 = true; }
                short f2 = n->getAnt2()->hasOccurrenceBin(n->getPivot());
                if (f2 != -1) { piv_in_ant2 = true; }
                assert(not(f1 == 1 and f2 == 1) and not(f1 == 0 and f2 == 0));

                if (piv_in_ant1 and piv_in_ant2) {
                    //Easy case: pivot still in both antecedents
                    //Sufficient to propagate modifications via merge
                    mergeClauses(n->getAnt1()->getClause(), n->getAnt2()->getClause(), n->getClause(), n->getPivot());
                    for (clauseid_t clauseid : n->getResolvents()) {
                        if (getNode(clauseid)) { q.push_back(clauseid); }
                    }
                    // NOTE extra check
                    if (proofCheck() > 1) checkClause(n->getId());
                } else {
                    assert(not piv_in_ant1 or not piv_in_ant2);
                    //Second case: pivot not in ant1 or not in ant2
                    //Remove resolution step, remove n, ant without pivots gains n resolvents
                    bool choose_ant1 = false;
                    //Pivot not in ant1 and not in ant2
                    if (not piv_in_ant1 and not piv_in_ant2) {
                        // Choose one of the two antecedents heuristically
                        choose_ant1 = chooseReplacingAntecedent(n);
                    } else {
                        choose_ant1 = not piv_in_ant1;
                    }

                    ProofNode * replacing = choose_ant1 ? n->getAnt1() : n->getAnt2();
                    ProofNode * other = choose_ant1 ? n->getAnt2() : n->getAnt1();

                    bool identicalParents = replacing == other; // MB: This is possible, test_recyclePivots_IdenticalAntecedents is an example.

                    replacing->remRes(id);
                    if (not identicalParents) {
                        other->remRes(id);
                    }

                    auto const & resolvents = n->getResolvents();
                    for (clauseid_t resId : resolvents) {
                        assert(resId < getGraphSize());
                        ProofNode * res = getNode(resId);
                        assert(res);
                        if (res->getAnt1() == n) { res->setAnt1(replacing); }
                        else if (res->getAnt2() == n) { res->setAnt2(replacing); }
                        else { throw OsmtInternalException("Invalid proof structure " + std::string(__FILE__) + ", " + std::to_string(__LINE__)); }
                        replacing->addRes(resId);
                        assert(not isSetVisited2(resId));
                        // Enqueue resolvent
                        q.push_back(resId);
                    }

                    //We might have reached old sink
                    //Case legal only if we have produced another empty clause
                    //Substitute old sink with new
                    if (isRoot(n)) {
                        assert(not identicalParents);
                        assert(replacing->getClauseSize() == 0);
                        setRoot(replacing->getId());
                        assert(n->getNumResolvents() == 0);
                        assert(replacing->getNumResolvents() == 0);
                    }
                    removeNode(n->getId());
                    if (not identicalParents and other->getNumResolvents() == 0) { removeTree(other->getId()); }
                    // NOTE extra check
                    if (proofCheck() > 1) checkClause(replacing->getId());
                }
            }
        } else { // Leaf node
            assert(isLeafClauseType(n->getType()));
            assert(n->getNumResolvents() > 0);
            for (clauseid_t clauseid : n->getResolvents()) {
                if (getNode(clauseid)) { q.push_back(clauseid); }
            }
        }
    } while (not q.empty());
    resetVisited2();

    if (proofCheck()) {
        unsigned rem = cleanProofGraph();
        if (rem > 0) std::cerr << "; Cleaned " << rem << " residual nodes" << std::endl;
        checkProof(true);
    }

    double endTime = cpuTime();

    if (verbose() > 1) {
        uint64_t mem_used = memUsed();
        reportf("; Memory used after restructuring: %.3f MB\n", mem_used == 0 ? 0 : mem_used / 1048576.0);
    }

    ////////////////////////////////////////////////////////////////////
    if (verbose() > 0) {
        unsigned new_n_nodes = 0;
        unsigned new_n_edges = 0;
        for (unsigned i = 0; i < getGraphSize(); i++) {
            ProofNode * pn = getNode(i);
            if (pn) {
                new_n_nodes++;
                new_n_edges += pn->getNumResolvents();
            }
        }
        std::cerr << "# RPI\t";
        std::cerr << "Nodes: " << new_n_nodes << "(-" << 100 * ((double) (num_nodes - new_n_nodes) / num_nodes)
                  << "%)\t";
        std::cerr << "Edges: " << new_n_edges << "(-" << 100 * ((double) (num_edges - new_n_edges) / num_edges)
                  << "%)\t";
        std::cerr << "Time: " << (endTime - initTime) << " s" << std::endl;
    }
    //////////////////////////////////////////////////////////////////

    return (endTime - initTime);
}

void ProofGraph::recycleUnits() {
    assert(mpz_cmp_ui(visited_1, 0) == 0 and mpz_cmp_ui(visited_2, 0) == 0);
    if (verbose() > 1) { std::cerr << "# " << "Recycle units begin" << '\n'; }
    if (verbose() > 1) {
        uint64_t mem_used = memUsed();
        reportf("# Memory used before recycling: %.3f MB\n", mem_used == 0 ? 0 : mem_used / 1048576.0);
    }

    double initTime = cpuTime();
    bool some_transf_done = true;
    long curr_num_loops = 0;

    std::set<clauseid_t> units_collected;
    std::deque<clauseid_t> q;
    // Main external loop
    while (some_transf_done) {
        // Enqueue leaves first
        q.assign(leaves_ids.begin(), leaves_ids.end());
        some_transf_done = false;
        do {
            clauseid_t id = q.front();
            assert(id < getGraphSize());
            q.pop_front();
            ProofNode *n = getNode(id);
            //Node not visited yet
            if (n and not isSetVisited1(id)) {
                // Wait if one antecedent is not visited yet;
                // the node will be enqueued anyway by that antecedent
                if (n->getAnt1() != nullptr and not isSetVisited1(n->getAnt1()->getId())) {/* skip */}
                else if (n->getAnt2() != nullptr and not isSetVisited1(n->getAnt2()->getId())) {/* skip */}
                else { // both antecedents visited, mark node as visited
                    setVisited1(id);
                    // Enqueue resolvents
                    for (clauseid_t rid : n->getResolvents()) {
                        if (getNode(rid)) { q.push_back(rid); }
                    }
                    // Non leaf node
                    if (n->getAnt1() or n->getAnt2()) {
                        assert(n->getAnt1());
                        assert(n->getAnt2());
                        assert((n->getAnt1()->getAnt1() and n->getAnt1()->getAnt2()) or
                               (n->getAnt1()->getAnt1() == nullptr and n->getAnt1()->getAnt2() == nullptr));
                        assert((n->getAnt2()->getAnt1() and n->getAnt2()->getAnt2()) or
                               (n->getAnt2()->getAnt1() == nullptr and n->getAnt2()->getAnt2() == nullptr));

                        //Look for pivot in antecedents
                        bool piv_in_ant1 = false;
                        bool piv_in_ant2 = false;

                        short f1 = n->getAnt1()->hasOccurrenceBin(n->getPivot());
                        if (f1 != -1) { piv_in_ant1 = true; }
                        short f2 = n->getAnt2()->hasOccurrenceBin(n->getPivot());
                        if (f2 != -1) { piv_in_ant2 = true; }
                        assert(not(f1 == 1 and f2 == 1) and not(f1 == 0 and f2 == 0));

                        //Easy case: pivot still in both antecedents
                        //Sufficient to propagate modifications via merge
                        if (piv_in_ant1 and piv_in_ant2) {
                            if (isSetVisited2(n->getAnt1()->getId()) or isSetVisited2(n->getAnt2()->getId())) {
                                mergeClauses(n->getAnt1()->getClause(), n->getAnt2()->getClause(), n->getClause(),
                                             n->getPivot());
                                setVisited2(id);
                            }
                            // Check whether an antecedent is a unit clause
                            // If so, v is replaced by the other antecedent
                            // and the literal gets propagated down
                            if (n->getAnt1()->getClauseSize() == 1 or n->getAnt2()->getClauseSize() == 1) {
                                some_transf_done = true;
                                bool choose_ant1 = n->getAnt2()->getClauseSize() == 1;

                                ProofNode *replacing = choose_ant1 ? n->getAnt1() : n->getAnt2();
                                ProofNode *other = choose_ant1 ? n->getAnt2() : n->getAnt1();
                                // Keep track of the unit clause detached
                                units_collected.insert(other->getId());

                                replacing->remRes(id);
                                other->remRes(id);

                                auto const &resolvents = n->getResolvents();
                                setVisited2(replacing->getId());
                                for (clauseid_t clauseid : resolvents) {
                                    assert(clauseid < getGraphSize());
                                    ProofNode *res = getNode(clauseid);
                                    assert(res);
                                    if (res->getAnt1() == n) { res->setAnt1(replacing); }
                                    else if (res->getAnt2() == n) { res->setAnt2(replacing); }
                                    else opensmt_error_();
                                    assert(res->getAnt1() != res->getAnt2());
                                    replacing->addRes(clauseid);
                                }
                                //We might have reached old sink
                                //Substitute old sink with new
                                if (isRoot(n)) {
                                    setRoot(replacing->getId());
                                    assert(n->getNumResolvents() == 0);
                                    assert(replacing->getNumResolvents() == 0);
                                }
                                removeNode(id);
                            }
                        }
                            //Second case: pivot not in ant1 or not in ant2
                            //Remove resolution step, remove n, ant without pivots gains n resolvents
                        else {
                            assert(not piv_in_ant1 or not piv_in_ant2);
                            //Pivot not in ant1 and not in ant2
                            bool choose_ant1 = false;
                            if (not piv_in_ant1 and not piv_in_ant2) {
                                // Choose one of the two antecedents heuristically
                                choose_ant1 = chooseReplacingAntecedent(n);
                            } else { // Choose the one not containing the pivot
                                choose_ant1 = not piv_in_ant1 and piv_in_ant2;
                            }

                            ProofNode *replacing = choose_ant1 ? n->getAnt1() : n->getAnt2();
                            ProofNode *other = choose_ant1 ? n->getAnt2() : n->getAnt1();

                            replacing->remRes(id);
                            other->remRes(id);

                            auto const &resolvents = n->getResolvents();
                            setVisited2(replacing->getId());

                            for (clauseid_t clauseid : resolvents) {
                                assert(clauseid < getGraphSize());
                                ProofNode *res = getNode(clauseid);
                                assert(res);
                                if (res->getAnt1() == n) { res->setAnt1(replacing); }
                                else if (res->getAnt2() == n) { res->setAnt2(replacing); }
                                else opensmt_error_();
                                assert(res->getAnt1() != res->getAnt2());
                                replacing->addRes(clauseid);
                            }
                            //We might have reached old sink
                            //Substitute old sink with new
                            if (isRoot(n)) {
                                setRoot(replacing->getId());
                                assert(n->getNumResolvents() == 0);
                                assert(replacing->getNumResolvents() == 0);
                            }
                            removeNode(n->getId());
                            if (other->getNumResolvents() == 0) { removeTree(other->getId()); }
                        }
                    }
                }
            }
        } while (not q.empty());
        // Visit vector
        resetVisited1();
        // To do only necessary merges, track modified nodes
        resetVisited2();
        // End loop
        curr_num_loops++;
    }

    //printClause(getRoot());
    // Readd each unit clause to restore the proof
    for (clauseid_t clauseid : units_collected) {
        ProofNode *unit = getNode(clauseid);
        ProofNode *oldroot = getRoot();
        // NOTE is it possible to have multiple unit clauses containing the same literal?
        // If so, which one should be readded?
        if (oldroot->getClauseSize() == 0) {
        } else {
            assert(oldroot->hasOccurrenceBin(var(unit->getClause()[0])) != -1);
            //printClause(unit);
            ProofNode *newroot = new ProofNode(logic_);
            newroot->initClause();
            if (produceInterpolants()) { newroot->initIData(); }
            newroot->setAnt1(oldroot);
            newroot->setAnt2(unit);
            newroot->setType(clause_type::CLA_DERIVED);
            newroot->setPivot(var((unit->getClause())[0]));
            newroot->setId(graph.size());
            graph.push_back(newroot);
            unit->addRes(newroot->getId());
            oldroot->addRes(newroot->getId());
            //newroot given by resolution of root and unit over v pivot
            mergeClauses(oldroot->getClause(), unit->getClause(), newroot->getClause(), newroot->getPivot());
            setRoot(newroot->getId());
        }
    }
    assert(getRoot()->getClauseSize() == 0);

    if (proofCheck()) {
        unsigned rem = cleanProofGraph();
        if (rem > 0) std::cerr << "# Cleaned " << rem << " residual nodes" << '\n';
        assert(rem == 0);
        checkProof(true);
    }
    double endTime = cpuTime();

    if (verbose() > 1) {
        uint64_t mem_used = memUsed();
        reportf("# Memory used after recycling: %.3f MB\n", mem_used == 0 ? 0 : mem_used / 1048576.0);
    }

    ////////////////////////////////////////////////////////////////////
    if (verbose() > 0) {
        unsigned new_n_nodes = 0;
        unsigned new_n_edges = 0;
        for (unsigned i = 0; i < getGraphSize(); i++) {
            ProofNode *pn = getNode(i);
            if (pn) {
                new_n_nodes++;
                new_n_edges += pn->getNumResolvents();
            }
        }

        std::cerr << "# LU\t";
        std::cerr << "Nodes: " << new_n_nodes << "(-" << 100 * ((double) (num_nodes - new_n_nodes) / num_nodes) << "%)\t";
        std::cerr << "Edges: " << new_n_edges << "(-" << 100 * ((double) (num_edges - new_n_edges) / num_edges) << "%)\t";
        std::cerr << "Traversals: " << curr_num_loops << "\t";
        std::cerr << "Time: " << (endTime - initTime) << " s" << '\n';
    }
    //////////////////////////////////////////////////////////////////
}


void ProofGraph::proofTransformAndRestructure(const double left_time, const int max_num_loops, bool do_transf,
        std::function<ApplicationResult(RuleContext&,RuleContext&)> handleRules)
{
    if (verbose() > 1) { std::cerr << "; " << "Proof transformation traversals begin" << std::endl; }
    if (verbose() > 1) {
        uint64_t mem_used = memUsed();
        reportf("; Memory used before proof transformation traversals: %.3f MB\n",
                mem_used == 0 ? 0 : mem_used / 1048576.0);
    }

    double init_time = cpuTime();
    assert(not (max_num_loops > 0 and left_time > 0));
    //Flag to check if in a loop at least a transformation has been applied
    bool some_transf_done = true;
    long curr_num_loops = 0;
    std::deque<clauseid_t> q;
    // Main external loop
    // Continue until
    // - max number of loops reached or timeout (in case of reduction)
    // - some transformation is done (in case of pivot reordering)
    while ((max_num_loops == -1 ? true : curr_num_loops < max_num_loops) and
           (left_time == -1 ? true : (cpuTime() - init_time) <= left_time) and
           (left_time != -1 or max_num_loops != -1 or some_transf_done))
    {
        assert(isResetVisited1() and isResetVisited2());
        // Enqueue leaves first
        q.assign(leaves_ids.begin(), leaves_ids.end());
        some_transf_done = false;
        while (not q.empty()) {
            clauseid_t id = q.front();
            assert(id < getGraphSize());
            q.pop_front();
            ProofNode * n = getNode(id);
            //Node not visited yet
            if (n and not isSetVisited1(id)) {
                // Wait if one antecedent is not visited yet;
                // the node will be enqueued anyway by that antecedent
                if ((n->getAnt1() and not isSetVisited1(n->getAnt1()->getId()))
                    or (n->getAnt2() and not isSetVisited1(n->getAnt2()->getId()))) {
                    continue;
                }
                // ELSE, both antecedents ready, process the node
                // Mark node as visited
                setVisited1(id);
                // Non leaf node
                if ((n->getAnt1() or n->getAnt2())) {
                    assert(n->getAnt1());
                    assert(n->getAnt2());
                    assert((n->getAnt1()->getAnt1() and n->getAnt1()->getAnt2())
                           or (not n->getAnt1()->getAnt1() and not n->getAnt1()->getAnt2()));
                    assert((n->getAnt2()->getAnt1() and n->getAnt2()->getAnt2())
                           or (not n->getAnt2()->getAnt1() and not n->getAnt2()->getAnt2()));

                    //Look for pivot in antecedents
                    short f1 = n->getAnt1()->hasOccurrenceBin(n->getPivot());
                    bool piv_in_ant1 = (f1 != -1);
                    short f2 = n->getAnt2()->hasOccurrenceBin(n->getPivot());
                    bool piv_in_ant2 = (f2 != -1);
                    assert(not(f1 == 1 and f2 == 1) and not(f1 == 0 and f2 == 0));
                    if (piv_in_ant1 and piv_in_ant2) {
                        //Easy case: pivot still in both antecedents
                        //Sufficient to propagate modifications via merge
                        for (clauseid_t resolvent : n->getResolvents()) {
                            if (getNode(resolvent)) { q.push_back(resolvent); }
                        }

                        if (isSetVisited2(n->getAnt1()->getId()) or isSetVisited2(n->getAnt2()->getId())) {
                            mergeClauses(n->getAnt1()->getClause(), n->getAnt2()->getClause(), n->getClause(), n->getPivot());
                            setVisited2(id);
                        }
                        // NOTE extra check
                        if (proofCheck() > 1) { checkClause(n->getId()); }

                        if (do_transf) {
                            RuleContext ra1 = getRuleContext(n->getAnt1()->getId(), n->getId());
                            RuleContext ra2 = getRuleContext(n->getAnt2()->getId(), n->getId());

                            auto chosen = handleRules(ra1, ra2);

                            rul_type app_rule = rNO;
                            if (chosen != ApplicationResult::NO_APPLICATION) {

                                assert(chosen == ApplicationResult::APPLY_FIRST || chosen == ApplicationResult::APPLY_SECOND);
                                RuleContext & chosen_ra = chosen == ApplicationResult::APPLY_FIRST ? ra1 : ra2;
                                app_rule = chosen_ra.getType();
                                clauseid_t dupl_id = 0;
                                if (getNode(chosen_ra.getW())->getNumResolvents() > 1 && isSwapRule(app_rule)) {
                                    dupl_id = dupliNode(chosen_ra);
                                }
                                clauseid_t A1_new_id = ruleApply(chosen_ra);
                                some_transf_done = true;

                                // NOTE see ProofGraphRules B3
                                // Mark v as modified
                                if (app_rule == rB1 or app_rule == rB2 or app_rule == rB2prime) { setVisited2(id); }
                                // Remember that in B3 v2 replaces v
                                if (app_rule == rB3) {
                                    setVisited2(chosen_ra.getV2());
                                }

                                // NOTE nodes might have been added on the fly by A1 and/or duplication
                                if (dupl_id != 0) {
                                    // The new node created by duplicating w has replaced w and will not be used elsewhere
                                    //visited_1.set(dupl_id); visited_2.reset(dupl_id);
                                }
                                if (A1_new_id != 0) {
                                    // The new node created by A1 is already updated and will not be used elsewhere
                                    //visited_1.set(A1_new_id); visited_2.reset(A1_new_id);
                                }
                            }
                            // NOTE extra check
                            if (proofCheck() > 1 && app_rule != rB3) { checkClause(n->getId()); }
                        }
                    } else {
                        //Second case: pivot not in ant1 or not in ant2
                        assert(not piv_in_ant1 or not piv_in_ant2);
                        //Remove resolution step, remove n, ant without pivots gains n resolvents
                        bool choose_ant1 = false;
                        if (not piv_in_ant1 and not piv_in_ant2) {
                            // Choose one of the two antecedents heuristically
                            choose_ant1 = chooseReplacingAntecedent(n);
                        } else {
                            choose_ant1 = not piv_in_ant1;
                        }
                        ProofNode * replacing = choose_ant1 ? n->getAnt1() : n->getAnt2();
                        ProofNode * other = choose_ant1 ? n->getAnt2() : n->getAnt1();
                        bool identicalParents = replacing == other; // MB: This is possible, test_proofTransformAndRestructure_IdenticalAntecedents is an example.

                        replacing->remRes(id);
                        if (not identicalParents) {
                            other->remRes(id);
                        }

                        auto const & resolvents = n->getResolvents();
                        setVisited2(replacing->getId());

                        for (clauseid_t resolvent : resolvents) {
                            assert(resolvent < getGraphSize());
                            ProofNode * res = getNode(resolvent);
                            assert(res);
                            assert(res->getAnt1() == n or res->getAnt2() == n);
                            if (res->getAnt1() == n) { res->setAnt1(replacing); }
                            else if (res->getAnt2() == n) { res->setAnt2(replacing); }
                            else { throw OsmtInternalException("Invalid proof structure " + std::string(__FILE__) + ", " + std::to_string(__LINE__)); }
                            replacing->addRes(resolvent);
                            q.push_back(resolvent);
                        }

                        //We might have reached old sink
                        //Case legal only if we have produced another empty clause
                        //Substitute old sink with new
                        if (isRoot(n)) {
                            assert(not identicalParents);
                            assert(replacing->getClauseSize() == 0);
                            setRoot(replacing->getId());
                            assert(n->getNumResolvents() == 0);
                            assert(replacing->getNumResolvents() == 0);
                        }
                        removeNode(n->getId());
                        if (not identicalParents and other->getNumResolvents() == 0) { removeTree(other->getId()); }
                        // NOTE extra check
                        if (proofCheck() > 1) { checkClause(replacing->getId()); }
                    }
                } else {
                    for (clauseid_t resolvent : n->getResolvents())
                        if (getNode(resolvent) != nullptr) { q.push_back(resolvent); }
                }
            }
        }
        // Visit vector
        resetVisited1();
        // To do only necessary merges, track modified nodes
        resetVisited2();

        // End loop
        curr_num_loops++;

        if (proofCheck() > 1) {
            std::cerr << "; Checking proof after loop " << curr_num_loops << std::endl;
            unsigned rem = cleanProofGraph();
            if (rem > 0) std::cerr << "; Cleaned " << rem << " residual nodes" << std::endl;
            checkProof(true);
        }
    }

    if (proofCheck()) {
        unsigned rem = cleanProofGraph();
        if (rem > 0) std::cerr << "; Cleaned " << rem << " residual nodes" << std::endl;
        //assert( rem == 0 );
        checkProof(true);
    }
    double endTime = cpuTime();

    if (verbose() > 1) {
        uint64_t mem_used = memUsed();
        reportf("; Memory used after proof transformation traversals: %.3f MB\n",
                mem_used == 0 ? 0 : mem_used / 1048576.0);
    }

    /////////////////////////////////////////////////////////////////////////////
    if (verbose() > 0) {
        unsigned new_n_nodes = 0;
        unsigned new_n_edges = 0;
        for (unsigned i = 0; i < getGraphSize(); i++) {
            ProofNode * pn = getNode(i);
            if (pn) {
                new_n_nodes++;
                new_n_edges += pn->getNumResolvents();
            }
        }

        std::cerr << "; RE\t";
        if (num_nodes >= static_cast<int>(new_n_nodes)) {
            std::cerr << "Nodes: " << new_n_nodes << "(-" << 100 * ((double) (num_nodes - new_n_nodes) / num_nodes)
                      << "%)\t";
        } else {
            std::cerr << "Nodes: " << new_n_nodes << "(+" << 100 * ((double) (new_n_nodes - num_nodes) / num_nodes)
                      << "%)\t";
        }
        if (num_edges >= static_cast<int>(new_n_edges)) {
            std::cerr << "Edges: " << new_n_edges << "(-" << 100 * ((double) (num_edges - new_n_edges) / num_edges)
                      << "%)\t";
        } else {
            std::cerr << "Edges: " << new_n_edges << "(+" << 100 * ((double) (new_n_edges - num_edges) / num_edges)
                      << "%)\t";
        }
        std::cerr << "Traversals: " << curr_num_loops << "\t";
        std::cerr << "Time: " << (endTime - init_time) << " s" << std::endl;
    }
    ///////////////////////////////////////////////////////////////////////////////
}

void ProofGraph::proofPostStructuralHashing()
{
	if ( verbose() > 1 ) std::cerr << "; Post-processing structural hashing begin" << std::endl;
	if ( verbose() > 1 )
	{
		uint64_t mem_used = memUsed();
		reportf( "; Memory used before structural hashing: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
	}

	double initTime = cpuTime();
	std::vector<clauseid_t> q;
	clauseid_t id;
	ProofNode* n = nullptr;
	// Map to associate node to its antecedents
	std::map< std::pair<clauseid_t,clauseid_t>, clauseid_t> ants_map;

	// NOTE Topological visit and node replacement on the fly
	// Guarantees that both replacing and replaced node subproofs have been visited
	q.push_back(getRoot()->getId());
	do
	{
		id=q.back();
		n=getNode(id);
		//Node not visited yet
		if(!isSetVisited1(id))
		{
			// Enqueue antecedents if not visited
			if(n->getAnt1()!=NULL && !isSetVisited1(n->getAnt1()->getId()))
				q.push_back(n->getAnt1()->getId());
			else if(n->getAnt2()!=NULL && !isSetVisited1(n->getAnt2()->getId()))
				q.push_back(n->getAnt2()->getId());
			// Mark node as visited if both antecedents visited
			else
			{
				setVisited1(id);
				q.pop_back();
				assert(n);
				// Non leaf node
				if(!n->isLeaf())
				{
					bool found = false;
					clauseid_t c1, c2;
					if(n->getAnt1()->getId() <= n->getAnt2()->getId())
					{ c1 = n->getAnt1()->getId(); c2 = n->getAnt2()->getId(); }
					else
					{ c2 = n->getAnt1()->getId(); c1 = n->getAnt2()->getId(); }
					// Look for pair <ant1,ant2>
					std::pair<clauseid_t, clauseid_t> ant_pair (c1,c2);
					auto it = ants_map.find(ant_pair);
					found = ( it != ants_map.end() );
					// If pairs not found, add node to the map
					if( !found ) ants_map[ ant_pair ] = id ;
					// else replace node with existing one
					else
					{
						ProofNode* replacing = getNode( it->second );
						assert( replacing );
						// Move n children to replacing node
						for(clauseid_t resolvent_id : n->getResolvents())
						{
							assert(resolvent_id < getGraphSize());
							ProofNode* res = getNode(resolvent_id);
							assert( res );
							if(res->getAnt1() == n) res->setAnt1( replacing );
							else if (res->getAnt2() == n) res->setAnt2( replacing );
							else opensmt_error_();
							replacing->addRes(resolvent_id);
						}
						n->getAnt1()->remRes(id);
						n->getAnt2()->remRes(id);
						removeNode(id);
					}
				}
			}
		}
		else q.pop_back();
	}
	while(!q.empty());
	resetVisited1();

	if( proofCheck() )
	{
		unsigned rem = cleanProofGraph( );
		if(rem > 0 ) std::cerr << "; Cleaned " << rem << " residual nodes" << std::endl;
		//assert( rem == 0 );
		checkProof( true );
	}
	double endTime = cpuTime();


	if ( verbose() > 1 )
	{
		uint64_t mem_used = memUsed();
		reportf( "; Memory used after structural hashing: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
	}

	/////////////////////////////////////////////////////////////////////////////
	if( verbose() > 0 )
	{
		unsigned new_n_nodes=0;
		unsigned new_n_edges=0;
		for(unsigned i = 0; i < getGraphSize(); i++)
		{
			ProofNode* pn = getNode(i);
			if(pn != NULL){ new_n_nodes++; new_n_edges += pn->getNumResolvents(); }
		}

		std::cerr << "; SH\t";
        std::cerr << "Nodes: " << new_n_nodes << "(-" << 100*((double)(num_nodes - new_n_nodes)/num_nodes) << "%)\t";
        std::cerr << "Edges: " << new_n_edges << "(-" << 100*((double)(num_edges - new_n_edges)/num_edges) << "%)\t";
        std::cerr << "Time: " << (endTime-initTime) << " s" << std::endl;
	}
	///////////////////////////////////////////////////////////////////////////////
}


namespace{
class LightVars {
public:

    template<typename TIt>
    LightVars(TIt begin, TIt end) {
        lights.insert(begin, end);
    }

    bool isLight(Var v) const { return lights.find(v) != lights.end(); }

private:
    std::unordered_set<Var> lights;
};

class LiftingVarsRuleHandler {
public:
    LiftingVarsRuleHandler(ProofGraph & pg, LightVars const & lv) : proofGraph(pg), lightVars(lv) {}

    ProofGraph::ApplicationResult operator()(RuleContext & ra1, RuleContext & ra2);

private:
    ProofGraph & proofGraph;
    LightVars const & lightVars;
};

using ApplicationResult = ProofGraph::ApplicationResult;


ApplicationResult LiftingVarsRuleHandler::operator()(RuleContext &ra1, RuleContext &ra2) {
    auto isUnordered = [this] (RuleContext const& ra) {
        Var lowerPivot = this->proofGraph.getNode(ra.getV())->getPivot();
        Var upperPivot = this->proofGraph.getNode(ra.getW())->getPivot();
        return this->lightVars.isLight(lowerPivot) && !this->lightVars.isLight(upperPivot);
    };
    bool enabled1 = ra1.enabled() && isUnordered(ra1);
    bool enabled2 = ra2.enabled() && isUnordered(ra2);
    if (!enabled1) {
        return enabled2 ? ApplicationResult::APPLY_SECOND : ApplicationResult::NO_APPLICATION;
    }
    // ra1 is enabled
    if (!enabled2) { return ApplicationResult::APPLY_FIRST; }
    // BOTH are enabled, pick better
    rul_type t1 = ra1.getType();
    rul_type t2 = ra2.getType();
    if (isCutRule(t1)) { return ApplicationResult::APPLY_FIRST; }
    if (isCutRule(t2)) { return ApplicationResult::APPLY_SECOND; }
    assert(isSwapRule(t1) && isSwapRule(t2));
    // Prefer simple swaps
    if (t1 == rA2) { return ApplicationResult::APPLY_FIRST; }
    if (t2 == rA2) { return ApplicationResult::APPLY_SECOND; }
    // No further rules, just pick first one
    return ApplicationResult::APPLY_FIRST;
}
}


void ProofGraph::liftVarsToLeaves(std::vector<Var> const & vars) {
    LightVars lightVars (vars.begin(), vars.end());
    LiftingVarsRuleHandler handler(*this, lightVars);
    proofTransformAndRestructure(-1, -1, true, handler);
}

void ProofGraph::replaceSubproofsWithNoPartitionTheoryVars(std::vector<Var> const & vars) {
    auto mustBeEliminated = [&vars](Var v) { return std::find(std::begin(vars), std::end(vars), v) != std::end(vars); };
    std::deque<clauseid_t> toProcess;
    toProcess.assign(this->leaves_ids.begin(), this->leaves_ids.end());
    resetVisited1();
    while (!toProcess.empty()) {
        clauseid_t current_id = toProcess.front();
        toProcess.pop_front();
        setVisited1(current_id);

        ProofNode * leaf = this->getNode(current_id);
        assert(leaf);
        assert(leaf->isLeaf());
        bool hasMixed = false;
        for (Var v : vars) {
            short present = leaf->hasOccurrenceBin(v);
            hasMixed |= (present != -1);
        }
        if (!hasMixed) { continue; }
        auto resolvents_ids = leaf->getResolvents();
        for (auto resolvent_id : resolvents_ids) {
            ProofNode * resolvent = this->getNode(resolvent_id);
            assert(resolvent);
            assert(mustBeEliminated(resolvent->getPivot())); // MB: While there is a problematic variable in the clause, all resolution steps must be on a problematic var
            if (!mustBeEliminated(resolvent->getPivot())) {
                opensmt_error("Error in post-processing in the proof: Lifting orphaned theory variables did not work properly");
            }
            // resolvent must be theory valid lemma, make it new leaf
            ProofNode * ant1 = resolvent->getAnt1();
            ProofNode * ant2 = resolvent->getAnt2();
            assert(ant1 && ant2);
            // only continue if both antecedents has been processed already!
            if (!isSetVisited1(ant1->getId()) || !isSetVisited1(ant2->getId())) {
                // This resolvent will be processed when the second antecedent is taken from the queue
                continue;
            }
            assert(ant1->getType() == clause_type::CLA_THEORY);
            assert(ant2->getType() == clause_type::CLA_THEORY);
            assert(ant1->isLeaf() && ant2->isLeaf());
            ant1->remRes(resolvent_id);
            ant2->remRes(resolvent_id);
            if (ant1->getNumResolvents() == 0) { this->removeNode(ant1->getId()); }
            if (ant2->getNumResolvents() == 0) { this->removeNode(ant2->getId()); }
            resolvent->setType(clause_type::CLA_THEORY);
            resolvent->setAnt1(nullptr);
            resolvent->setAnt2(nullptr);
            this->addLeaf(resolvent_id);
            toProcess.push_back(resolvent_id);
        }
    }
    resetVisited1();
}

