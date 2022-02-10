//
// Created by prova on 08.02.19.
//

#ifndef OPENSMT_LOOKAHEADSPLITTER_H
#define OPENSMT_LOOKAHEADSPLITTER_H

#include "LookaheadSMTSolver.h"

class LookaheadSplitter : public LookaheadSMTSolver {
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

public:
    LookaheadSplitter(SMTConfig& c, THandler& thandler) : LookaheadSMTSolver(c, thandler) {}
};

#endif //OPENSMT_LOOKAHEADSPLITTER_H
