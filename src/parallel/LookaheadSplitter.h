/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef PARALLEL_LOOKAHEADSPLITTER_H
#define PARALLEL_LOOKAHEADSPLITTER_H

#include "LookaheadSMTSolver.h"
#include "SplitData.h"
#include "Splitter.h"

static inline int getLog2Ceil(int i)
{
    if (i == 0 || i == 1) return 0;
    int r = 0;
    int j = i;
    while (i >>= 1) r++;

    if ((1 << r) ^ j) r++;
    return r;
}

class LookaheadSplitter : public LookaheadSMTSolver, public Splitter {

public:
    LookaheadSplitter(SMTConfig& c, THandler& thandler)
    : Splitter(c)
    , LookaheadSMTSolver(c, thandler)
    {}

protected:
    LALoopRes solveLookahead() override;
    class LASplitNode : public LookaheadSMTSolver::LANode {
        static inline unsigned numNodes = 0;
        unsigned id;
    public:
        LASplitNode() : id(numNodes++) {}
        std::unique_ptr<SplitData> sd;
        LASplitNode * getParent() override { return (LASplitNode*)p; }
        unsigned getId() const { return id; }

        void print_local() const override {
            LANode::print_local();
            for (int i = 0; i < d; i++)
                dprintf(STDERR_FILENO, " ");
            dprintf(STDERR_FILENO, "%s\n", sd == nullptr ? "no instance" : "has instance" );
        }
        LASplitNode const * getC1() const { return (LASplitNode*) c1.get(); }
        LASplitNode const * getC2() const { return (LASplitNode*) c2.get(); }
        struct Hash {
            uint32_t operator ()(LASplitNode const * p) const { return (uint32_t)p->getId(); }
        };
    };

    void copySplits(LASplitNode const & root);

    bool createSplitLookahead(LASplitNode &);

    struct SplitBuildConfig {
    private:
        LookaheadSplitter & splitter;
    public:
        bool stopCondition(LASplitNode & n, int num_split) {
            int maxDepth = getLog2Ceil(num_split);
            if (n.d == maxDepth) {
#ifdef LADEBUG
                printf("Producing a split:\n");;
            printTrace();
#endif
                splitter.createSplitLookahead(n);
                return true;
            }
            return false;
        }
        LALoopRes exitState() const { return LALoopRes::unknown_final; }
        SplitBuildConfig(LookaheadSplitter & splitter_) : splitter(splitter_) {}
    };
};

#endif //PARALLEL_LOOKAHEADSPLITTER_H
