/*
 *  Copyright (c) 2013, Simone Fulvio Rollini <simone.rollini@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "PG.h"

#include "SystemQueries.h"
#include "OsmtInternalException.h"
#include "ReportUtils.h"

#include <deque>

std::ostream& operator<< (std::ostream &out, RuleContext &ra)
{
    out << "Context: v1(" << ra.getV1() << ") v2(" << ra.getV2() << ") w("
        << ra.getW() << ") v3(" << ra.getV3() << ") v("
        << ra.getV() << ")";
    return out;
}

namespace{
struct ProofBuildingStatistics {
    unsigned num_leaf = 0;
    unsigned num_theory = 0;
    unsigned num_derived = 0;
    unsigned num_learnt = 0;
    unsigned num_assump = 0;
    unsigned num_split = 0;

    void recordNewClause(clause_type typ) {
        switch(typ) {
            case clause_type::CLA_ORIG:
                ++num_leaf;
                break;
            case clause_type::CLA_THEORY:
                ++num_theory;
                break;
            case clause_type::CLA_LEARNT:
                ++num_learnt;
                break;
            case clause_type::CLA_DERIVED:
                ++num_derived;
                break;
            case clause_type::CLA_ASSUMPTION:
                ++num_assump;
                break;
            case clause_type::CLA_SPLIT:
                ++num_split;
                break;
            default:
                assert(false);
                ;
        }
    }
};
}

ProofNode * ProofGraph::createProofNodeFor(CRef clause, clause_type _ctype, ResolutionProof const & proof) {
    ProofNode * n = new ProofNode();
    if (isLeafClauseType(_ctype)) {
        n->initClause(proof.getClause(clause));
        n->setClauseRef(clause);
        //Sort clause literals
        std::sort(n->getClause().begin(),n->getClause().end());
    }

    //Add node to graph vector
    auto currId = static_cast<clauseid_t>(graph.size());
    graph.push_back(n);
    n->setId(currId);
    assert(getNode(currId) == n);
    return n;
}

void ProofGraph::buildProofGraph(const ResolutionProof & proof) {
    if (verbose()) { std::cerr << "# " << "Proof graph building begin" << '\n'; }
    if (verbose() > 0) {
        uint64_t mem_used = memUsed();
        reportf("# Memory used before building the proof: %.3f MB\n", mem_used == 0 ? 0 : mem_used / 1048576.0);
    }

    const double initTime=cpuTime();
    max_id_variable=0;

    av_cla_size=0; max_cla_size=0;
    num_edges=0;
    num_nodes=0;
    num_leaves=0;
    building_time=0;

    A1=0;
    A1prime=0;
    A1B=0;
    A2=0;
    A2B=0;
    A2U=0;
    B1=0;
    B2prime=0;
    B2=0;
    B3=0;
    duplications=0;
    swap_ties=0;

    auto const & clause_to_proof_der = proof.getProof();

    //To map clauses to graph id
    //An id is associated when the node is created
    std::map<CRef, clauseid_t> clauseToIDMap;
    //To keep track of visited nodes
    std::set<CRef> visitedSet;
    //Queue to build proof graph from sink
    std::deque<CRef> q;

    ProofBuildingStatistics counters;

    unsigned      max_leaf_size = 0;
    double        avg_leaf_size = 0;
    unsigned      max_learnt_size = 0;
    double        avg_learnt_size = 0;

    // NOTE: Must guarantee first antecedent -> positive occurrence pivot
    // second antecedent -> negative occurrence pivot

    // Map to associate node to its antecedents
    std::map< std::pair<int,int>, int > ants_map;
    //Start from empty clause
    {
        auto it = clause_to_proof_der.find(CRef_Undef);
        if (it == clause_to_proof_der.end()) { throw OsmtInternalException("Proof building: Empty clause was not derived!"); }
        if (it->second.isEmpty()) { throw OsmtInternalException("Proof building: Empty clause has no chain!"); }
    }

    // Helper method to process clause seen for the first time
    auto processNewClause = [&](CRef clause) {
        clause_type _ctype = clause_to_proof_der.at(clause).type;
        counters.recordNewClause(_ctype);
        ProofNode *n = createProofNodeFor(clause, _ctype, proof);
        if (isLeafClauseType(_ctype)) {
            if (n->getClauseSize() >= max_leaf_size) {
                max_leaf_size = n->getClauseSize();
            }
            avg_leaf_size += n->getClauseSize();
        } else if (_ctype == clause_type::CLA_LEARNT) {
            unsigned ssize = clause != CRef_Undef ? proof.getClause(clause).size() : 0;
            if (ssize >= max_learnt_size) { max_learnt_size = ssize; }
            avg_learnt_size += ssize;
        } else {
            assert(false);
        }
        clauseToIDMap[clause] = n->getId();
        q.push_back(clause);
    };
    processNewClause(CRef_Undef);

    do {
        CRef currClause = q.back();
        q.pop_back();
        if (visitedSet.find(currClause) != visitedSet.end()) { continue; }

        assert(clause_to_proof_der.find(currClause) != clause_to_proof_der.end());
        auto const & proofder = clause_to_proof_der.at(currClause); // Derivation
        auto const & chaincla = proofder.chain_cla;            // Clauses chain
        auto const & chainvar = proofder.chain_var;            // Pivot chain
        clause_type ctype = proofder.type;

        if (isLeafClauseType(ctype)) {
            assert(chaincla.empty());
            // MB: Proof built from the root towards the leaves.
            //     A leaf node is constructed when its first children is constructred. Here it must already exist.
            auto it = clauseToIDMap.find(currClause);
            assert(it != clauseToIDMap.end());
            getNode(it->second)->setType(ctype);
            addLeaf(it->second);
        } else if (ctype == clause_type::CLA_LEARNT) {
            assert(chaincla.size() >= 2);
            assert(chainvar.size() == chaincla.size() - 1);

            // TODO: Check if this is not redundant in current implementation
            auto skipChainsOfLengthOne = [&clause_to_proof_der](CRef cref) -> CRef {
                while (clause_to_proof_der.at(cref).chain_cla.size() == 1) {
                    cref = clause_to_proof_der.at(cref).chain_cla[0];
                }
                return cref;
            };

            CRef clause_0 = skipChainsOfLengthOne(chaincla[0]);
            if (clauseToIDMap.find(clause_0) == clauseToIDMap.end()) {
                processNewClause(clause_0);
            }
            auto last_seen_id = clauseToIDMap.at(clause_0);
            // Check for internally deduced clauses
            for (std::size_t i = 1; i < chaincla.size(); ++i) {
                // ith clause not yet processed
                CRef clause_i = skipChainsOfLengthOne(chaincla[i]);

                if (clauseToIDMap.find(clause_i) == clauseToIDMap.end()) {
                    processNewClause(clause_i);
                }
                ProofNode *n = nullptr;
                clauseid_t currId = static_cast<clauseid_t>(-1);

                // End tree not reached: deduced node
                if (i < chaincla.size() - 1) {
                    currId = graph.size();
                    n = new ProofNode();
                    //Add node to graph vector
                    n->setId(currId);
                    graph.push_back(n);
                    assert(getNode(currId) == n);
                    n->setType(clause_type::CLA_DERIVED);
                    counters.recordNewClause(clause_type::CLA_DERIVED);
                } else { // End tree reached: currClause
                    if (clauseToIDMap.find(currClause) == clauseToIDMap.end()) {
                        assert(false);
                        throw OsmtInternalException("Error in proof building: Learnt clause not processed yet!");
                    }
                    currId = clauseToIDMap.at(currClause);
                    n = getNode(currId);
                    n->setType(clause_type::CLA_LEARNT);
                }
                assert(n);
                // Edges creation
                // First internal node deduced from first clauses 0 and 1
                // Other internal nodes deduced from last internal node and clause i
                Var pivot = chainvar[i - 1];
                n->setPivot(pivot);
                proof_variables.insert(pivot);
                if (static_cast<unsigned>(pivot) > max_id_variable) {
                    max_id_variable = static_cast<unsigned>(pivot);
                }
                assert(currId != static_cast<clauseid_t>(-1));
                assert(last_seen_id != currId);

                bool pos_piv = true;
                bool found_piv = false;
                // Make sure ant1 has the pivot positive (and ant2 negated)
                Clause & clausei = proof.getClause(clause_i);
                for (unsigned k = 0; k < clausei.size(); ++k) {
                    if (var(clausei[k]) == n->getPivot()) {
                        if (sign(clausei[k]) != 0) { pos_piv = false; }
                        found_piv = true;
                        break;
                    }
                }
                assert(found_piv); (void) found_piv;
                auto id_i = clauseToIDMap.at(clause_i);
                n->setAnt1(pos_piv ? getNode(id_i) : getNode(last_seen_id));
                n->setAnt2(pos_piv ? getNode(last_seen_id) : getNode(id_i));
                last_seen_id = currId;
                n->getAnt1()->addRes(n->getId());
                n->getAnt2()->addRes(n->getId());
            }
        } else {
            assert(false);
        }
        visitedSet.insert(currClause);
    } while(!q.empty());

    setRoot(clauseToIDMap.at(CRef_Undef));

    if (proofCheck()) {
        // Check whether there are any remaining pieces
        checkProof(false);
        unsigned rem = cleanProofGraph();
        assert(rem == 0);
        (void) rem;
    }

    if (verbose() > 0) {
        unsigned num_non_null = 0;
#ifdef PEDANTIC_DEBUG
        unsigned cl_non_null = 0;
#endif
        for (size_t i = 0; i < getGraphSize(); i++) {
            if (getNode(i)) {
                num_non_null++;
#ifdef PEDANTIC_DEBUG
                if (getNode(i)->getPClause()) {
                    cl_non_null++;
                }
#endif
            }
        }
#ifdef PEDANTIC_DEBUG
        cout << "Graph size: " << getGraphSize() << '\n';
        cout << "Non null nodes: " << num_non_null << '\n';
        cout << "Non null clauses: " << cl_non_null << '\n';
#endif
        if (graph.size() > 1) {
            assert(num_non_null == (counters.num_leaf + counters.num_learnt + counters.num_derived + counters.num_theory + counters.num_assump));
        }

        reportf("; Number of nodes: %d (leaves: %d - learnt: %d - derived: %d - theory: %d - assumptions: %d)\n",
                num_non_null, counters.num_leaf, counters.num_learnt, counters.num_derived, counters.num_theory,
                counters.num_assump);
        reportf("; Maximum, average size of leaves: %d  %.2f\n", max_leaf_size,
                avg_leaf_size / (double) counters.num_leaf);
        reportf("; Maximum, average size of learnt: %d  %.2f\n", max_learnt_size,
                avg_learnt_size / (double) counters.num_learnt);
        num_edges = (counters.num_learnt + counters.num_derived) * 2;
        reportf("; Number of edges: %d\n", num_edges);
        num_nodes = num_non_null;

        //reportf( "# Number of variables - nominal: %d - actual: %d\n",  num_vars_limit, proof_variables.size() );
        reportf("; Number of distinct variables in the proof: %d\n", (int) proof_variables.size());
    }
    if (verbose() > 0) {
        uint64_t mem_used = memUsed();
        reportf("; Memory used after building the proof: %.3f MB\n", mem_used == 0 ? 0 : mem_used / 1048576.0);
    }
    if (verbose()) { std::cerr << "; Proof graph building end" << std::endl; }
    building_time = cpuTime() - initTime;

    // Postprocessing of the proof

    this->addDefaultAssumedLiterals(proof.getAssumedLiterals());

    if (proofCheck()) {
        verifyLeavesInconsistency();
    }
}

void ProofGraph::fillProofGraph() {
    if (verbose() > 1) {
        uint64_t mem_used = memUsed();
        reportf("; Memory used before filling the proof: %.3f MB\n", mem_used == 0 ? 0 : mem_used / 1048576.0);
    }
    std::vector<clauseid_t> q;
    q.push_back(getRoot()->getId());
    do {
        clauseid_t id = q.back();
        ProofNode * n = getNode(id);
        //Node not visited yet
        if (not isSetVisited1(id)) {
            // Enqueue antecedents if not visited
            if (n->getAnt1() and not isSetVisited1(n->getAnt1()->getId())) {
                q.push_back(n->getAnt1()->getId());
            } else if (n->getAnt2() and not isSetVisited1(n->getAnt2()->getId())) {
                q.push_back(n->getAnt2()->getId());
            } else { // Mark node as visited if both antecedents visited
                setVisited1(id);
                q.pop_back();
                assert(n);
                //Non leaf node
                if (not n->isLeaf()) {
                    n->initClause();
                    mergeClauses(n->getAnt1()->getClause(), n->getAnt2()->getClause(), n->getClause(), n->getPivot());
                }
            }
        } else q.pop_back();
    } while (not q.empty());
    resetVisited1();

    if (verbose() > 0) {
        uint64_t mem_used = memUsed();
        reportf("; Memory used after filling the proof: %.3f MB\n", mem_used == 0 ? 0 : mem_used / 1048576.0);
    }
}

void ProofGraph::emptyProofGraph() {
    if (verbose() > 1) {
        uint64_t mem_used = memUsed();
        reportf("; Memory used before emptying the proof: %.3f MB\n", mem_used == 0 ? 0 : mem_used / 1048576.0);
    }
    for (size_t i = 0; i < getGraphSize(); ++i) {
        ProofNode * n = getNode(i);
        if (n and not n->isLeaf()) { n->resetClause(); }
    }
    if (verbose() > 0) {
        uint64_t mem_used = memUsed();
        reportf("; Memory used after emptying the proof: %.3f MB\n", mem_used == 0 ? 0 : mem_used / 1048576.0);
    }
}

void ProofGraph::normalizeAntecedentOrder() {
    // Normalize proof for interpolation
    std::deque<ProofNode *> q;
    q.push_back(getRoot());
    do {
        ProofNode * n = q.front();
        q.pop_front();
        if (not isSetVisited1(n->getId())) {
            if (not n->isLeaf()) {
                q.push_back(n->getAnt1());
                q.push_back(n->getAnt2());

                // Check pivot in antecedents
                short f1 = n->getAnt1()->hasOccurrenceBin(n->getPivot());
                short f2 = n->getAnt2()->hasOccurrenceBin(n->getPivot());
                assert(f1 != -1 && f2 != -1);
                assert(not (f1 == 1 and f2 == 1) and not(f1 == 0 and f2 == 0));
                // Exchange antecedents if necessary
                if (f1 == 1 and f2 == 0) {
                    ProofNode * aux = n->getAnt1();
                    n->setAnt1(n->getAnt2());
                    n->setAnt2(aux);
                }
            }
            setVisited1(n->getId());
        }
    } while (not q.empty());
    resetVisited1();
}

int ProofGraph::cleanProofGraph() {
    // Remove the unreachable part of the graph
    // Ideally it will be made of subgraphs not connected to the main graph
    unsigned removed = 0;
    bool done = false;
    while (not done) {
        done = true;
        for (size_t i = 0; i < getGraphSize(); i++) {
            if (getNode(i)  and getNode(i)->getNumResolvents() == 0 and getNode(i) != getRoot()) {
                done = false;
                removed += removeTree(i);
            }
        }
    }
    return removed;
}

//Remove a node from the graph
void ProofGraph::removeNode(clauseid_t vid) {
    ProofNode * n = getNode(vid);
    assert(n);
    if (n->getAnt1() == nullptr and n->getAnt2() == nullptr) {
        removeLeaf(vid);
    }
    n->setAnt1(nullptr);
    n->setAnt2(nullptr);
    delete n;
    // Remove n from proof
    graph[vid] = nullptr;
}

unsigned ProofGraph::removeTree(clauseid_t vid) {
    assert(getNode(vid));
    assert(getNode(vid)->getNumResolvents() == 0);
    unsigned removed = 0;

    //Go on removing nodes with 0 resolvents
    //Visit graph from root keeping track of edges and nodes
    std::deque<clauseid_t> q;
    // Better a set than a boolean vector to avoid wasting memory
    std::set<clauseid_t> visit;
    q.push_back(vid);
    do {
        clauseid_t c = q.front();
        q.pop_front();
        assert(c < getGraphSize());
        ProofNode * n = getNode(c);
        //Remove node if no more resolvents present
        if (n and n->getNumResolvents() == 0) {
            if (n->getAnt1()) {
                assert(getNode(n->getAnt1()->getId()) == n->getAnt1());
                q.push_back(n->getAnt1()->getId());
                n->getAnt1()->remRes(c);
            }
            if (n->getAnt2()) {
                assert(getNode(n->getAnt2()->getId()) == n->getAnt2());
                q.push_back(n->getAnt2()->getId());
                n->getAnt2()->remRes(c);
            }
            removeNode(c);
            removed++;
        }
    } while (not q.empty());
    return removed;
}

clauseid_t ProofGraph::dupliNode(RuleContext & ra) {
    clauseid_t v_id = ra.getV();
    ProofNode * w = getNode(ra.getW());
    assert(w);
    unsigned num_old_res = w->getNumResolvents();
    assert(num_old_res > 1); (void) num_old_res;
    for (clauseid_t resolvent_id : w->getResolvents()) {
        ProofNode * res = getNode(resolvent_id);
        assert(res); (void) res;
        assert(res->getAnt1() == w or res->getAnt2() == w);
    }
    // Create node and add to graph vector
    ProofNode * n = new ProofNode();
    clauseid_t currId = getGraphSize();
    n->setId(currId);
    graph.push_back(n);
    assert(getNode(currId) == n);
    n->setType(w->getType());
    n->initClause(w->getClause());
    n->setClauseRef(w->getClauseRef());

    // Set antecedents, pivot
    n->setAnt1(w->getAnt1());
    n->setAnt2(w->getAnt2());
    n->getAnt1()->addRes(currId);
    n->getAnt2()->addRes(currId);
    n->setPivot(w->getPivot());

    // The new node replaces w in the context
    // w loses v but keeps everything else
    ProofNode * v = getNode(v_id);
    w->remRes(v_id);
    n->addRes(v_id);
    if (v->getAnt1() == w) v->setAnt1(n);
    else if (v->getAnt2() == w) v->setAnt2(n);
    else throw OsmtInternalException("Error in node duplication");
    assert(w->getResolvents().find(v_id) == w->getResolvents().end());
    assert(w->getNumResolvents() == num_old_res - 1);
    // Remember to modify context
    ra.cw = currId;

    duplications++;
    return currId;
}

void ProofGraph::addDefaultAssumedLiterals(std::vector<Lit> && assumedLiteralsFromDerivations) {
    this->assumedLiterals = std::move(assumedLiteralsFromDerivations);
}

void ProofGraph::eliminateNoPartitionTheoryVars(std::vector<Var> const & noPartitionTheoryVars) {
    // Prepare the graph for transformations
    this->fillProofGraph();

    // First step: lift all resolution steps on these vars as close to leaves as possible to create subproofs
    // where resolution happens only on marked vars
    this->liftVarsToLeaves(noPartitionTheoryVars);

    // Second step: Replace the subproofs created in the first step with their root.
    // The leaves of each subproof must be theory clauses, so its root must also be a valid theory clause
    this->replaceSubproofsWithNoPartitionTheoryVars(noPartitionTheoryVars);

    // Cleanup
    this->emptyProofGraph();
    for (Var v : noPartitionTheoryVars) {
        this->proof_variables.erase(v);
    }
}
