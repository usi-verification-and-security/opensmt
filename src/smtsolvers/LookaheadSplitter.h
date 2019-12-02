//
// Created by prova on 08.02.19.
//

#ifndef OPENSMT_LOOKAHEADSPLITTER_H
#define OPENSMT_LOOKAHEADSPLITTER_H

#include "LookaheadSMTSolver.h"

class LookaheadSplitter : public LookaheadSMTSolver {
protected:
    LALoopRes solveLookahead() override;
    class LASplitNode : public LookaheadSMTSolver::LANode
    {
    public:
        // The children
        SplitData* sd;
        LASplitNode() : sd(nullptr) {}
        ~LASplitNode() override { delete sd; }
        void print_local() override {
            LANode::print_local();
            for (int i = 0; i < d; i++)
                dprintf(STDERR_FILENO, " ");
            dprintf(STDERR_FILENO, "%s\n", sd == nullptr ? "no instance" : "has instance" );
        }
        LASplitNode* getC1() { return (LASplitNode*) c1; }
        LASplitNode* getC2() { return (LASplitNode*) c2; }
    };
    void copySplits(LASplitNode *root);

    public:
    LookaheadSplitter(SMTConfig& c, THandler& thandler) : LookaheadSMTSolver(c, thandler) {}
    bool     createSplitLookahead(LASplitNode*);


};


#endif //OPENSMT_LOOKAHEADSPLITTER_H
