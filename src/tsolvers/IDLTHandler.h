//
// Created by Martin Blicha on 10.05.20.
//

#ifndef OPENSMT_IDLTHANDLER_H
#define OPENSMT_IDLTHANDLER_H

#include "TSolverHandler.h"

class LIALogic;
class IDLSolver;

class IDLTHandler : public TSolverHandler
{
private:
    LIALogic& logic;
    IDLSolver *idlsolver;
public:
    IDLTHandler(SMTConfig& c, LIALogic& l);
    virtual ~IDLTHandler() = default;
    virtual Logic& getLogic() override;
    virtual const Logic& getLogic() const override;
//    virtual lbool getPolaritySuggestion(PTRef) const override;
    virtual PTRef getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t>*, PartitionManager& pmanager) override {
        throw std::logic_error("Not implemented yet");
    }

};


#endif //OPENSMT_IDLTHANDLER_H
