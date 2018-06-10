#ifndef LIATHandler_H
#define LIATHandler_H

#include "TSolverHandler.h"

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
    virtual void fillTmpDeds(PTRef root, Map<PTRef,int,PTRefHash> &refs);
    virtual bool assertLit_special(PtAsgn);
    virtual Logic& getLogic();
    virtual const Logic& getLogic() const;

#ifdef PRODUCE_PROOF
    virtual TheoryInterpolator* getTheoryInterpolator()
    {
        return NULL;
    }
    virtual PTRef getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels);
#endif
};

#endif
