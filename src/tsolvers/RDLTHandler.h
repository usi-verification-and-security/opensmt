#ifndef OPENSMT_RDLTHANDLER_H
#define OPENSMT_RDLTHANDLER_H

#include "TSolverHandler.h"

class ArithLogic;
class RDLSolver;

class RDLTHandler : public TSolverHandler
{
private:
    ArithLogic& logic;
    RDLSolver *rdlsolver;
public:
    RDLTHandler(SMTConfig &c, ArithLogic &l);
    virtual ~RDLTHandler() = default;
    Logic &getLogic() override;
    const Logic &getLogic() const override;
    PTRef getInterpolant(const ipartitions_t &, map<PTRef, icolor_t>*, PartitionManager&) override {
        throw std::logic_error("Not implemented yet");
    }

};


#endif //OPENSMT_RDLTHANDLER_H
