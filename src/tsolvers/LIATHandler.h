#ifndef LIATHandler_H
#define LIATHandler_H

#include "TSolverHandler.h"

#include "ArithLogic.h"

class LIASolver;
class ArithLogic;

class LIATHandler : public TSolverHandler
{
  private:
    ArithLogic& logic;
    LIASolver *liasolver;
  public:
    LIATHandler(SMTConfig & c, ArithLogic & l);
    virtual ~LIATHandler();
    virtual Logic& getLogic() override;
    virtual const Logic& getLogic() const override;

    virtual PTRef getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels, PartitionManager &pmanager) override;
};

#endif
