//
// Created by Martin Blicha on 10.05.20.
//

#ifndef OPENSMT_IDLTHANDLER_H
#define OPENSMT_IDLTHANDLER_H

#include "TSolverHandler.h"

class LIALogic;
template<class T> class STPSolver;
class SafeInt;

class IDLTHandler : public TSolverHandler
{
private:
    LIALogic& logic;
    STPSolver<SafeInt> *idlsolver;
public:
    IDLTHandler(SMTConfig& c, LIALogic& l, TermMapper& tmap);
    virtual ~IDLTHandler() = default;
    virtual Logic& getLogic() override;
    virtual const Logic& getLogic() const override;
//    virtual lbool getPolaritySuggestion(PTRef) const override;
    virtual PTRef getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t>*) override {
        throw std::logic_error("Not implemented yet");
    }

};


#endif //OPENSMT_IDLTHANDLER_H
