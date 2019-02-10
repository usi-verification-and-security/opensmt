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
        SplitData* sd;
    };
    public:
    LookaheadSplitter(SMTConfig& c, THandler& thandler) : LookaheadSMTSolver(c, thandler) {}
    bool     createSplitLookahead(LASplitNode*);

};


#endif //OPENSMT_LOOKAHEADSPLITTER_H
