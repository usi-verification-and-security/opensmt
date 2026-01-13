#ifndef OPENSMT_RDLTHANDLER_H
#define OPENSMT_RDLTHANDLER_H

#include "TSolverHandler.h"

namespace opensmt {

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
    PTRef getInterpolantImpl(const ipartitions_t &, ItpColorMap *, PartitionManager&) override {
        throw std::logic_error("Not implemented yet");
    }

};

}

#endif //OPENSMT_RDLTHANDLER_H
