//
// Created by prova on 08.02.19.
//

#ifndef OPENSMT_LOOKAHEADSPLITTER_H
#define OPENSMT_LOOKAHEADSPLITTER_H

#include "LookaheadSMTSolver.h"

class LookaheadSplitter : public LookaheadSMTSolver {
public:
    LookaheadSplitter(SMTConfig& c, THandler& thandler) : LookaheadSMTSolver(c, thandler) {}
protected:
    LALoopRes solveLookahead() override;
};


#endif //OPENSMT_LOOKAHEADSPLITTER_H
