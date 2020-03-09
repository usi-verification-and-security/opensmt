#ifndef LIATHandler_H
#define LIATHandler_H

#include "TSolverHandler.h"

#include "LIALogic.h"

class LIASolver;
class LIALogic;

class LIATHandler : public TSolverHandler
{
  private:
    LIALogic& logic;
    LIASolver *liasolver;
  public:
    LIATHandler(SMTConfig& c, LIALogic& l, vec<DedElem>& d, TermMapper& tmap);
    virtual ~LIATHandler();
    virtual void fillTmpDeds(PTRef root, Map<PTRef,int,PTRefHash> &refs) override;
    virtual bool assertLit_special(PtAsgn) override;
    virtual Logic& getLogic() override;
    virtual const Logic& getLogic() const override;

    virtual PTRef getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels) override;
};

#endif
