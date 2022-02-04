//
// Created by prova on 08.02.19.
//

#include "LookaheadSplitter.h"

LookaheadSMTSolver::LALoopRes LookaheadSplitter::solveLookahead() {

    auto [result, node] = buildAndTraverse<LASplitNode, SplitBuildConfig>(SplitBuildConfig(*this));

    if (result == LALoopRes::unknown_final) {
        copySplits(*node);
        assert(static_cast<int>(splits.size()) == config.sat_split_num());
    }

    return result;
}

bool LookaheadSplitter::createSplitLookahead(LASplitNode & n)
{
    // Create a split instance and add it to node n.
    assert(n.sd == nullptr);
    n.sd = std::make_unique<SplitData>(config.smt_split_format_length() == spformat_brief);
    SplitData& sd = *n.sd;
    printf("; Outputing an instance:\n; ");
    Lit p = lit_Undef;
    for (int i = 0; i < decisionLevel(); i++) {
        vec<Lit> tmp;
        Lit l = trail[trail_lim[i]];
        if (p != l) {
            // In cases where the LA solver couldn't propagate due to
            // literal being already assigned, the literal may be
            // duplicated.  Do not report duplicates.
            tmp.push(l);
            printf("%s%d ", sign(l) ? "-" : "", var(l));
            sd.addConstraint(tmp);
        }
        p = l;
    }
    printf("\n");

    assert(ok);
    return true;
}

void LookaheadSplitter::copySplits(LASplitNode const & root)
{

    vec<LASplitNode const *> queue;
    queue.push(&root);

    Map <LASplitNode const *,bool,LASplitNode::Hash> seen;

    // This is buggy: We need to pop the instances once all their children have been processed.
    while (queue.size() != 0) {
        LASplitNode const * n = queue.last();
        if (!seen.has(n)) {
            seen.insert(n, true);
            if (n->c1 != nullptr) {
                assert(n->c2 != nullptr);
                queue.push(n->getC1());
                queue.push(n->getC2());
            }
            continue;
        }
        queue.pop();
        if (n->sd != nullptr)
            splits.emplace_back(std::move(*n->sd));
    }
}

