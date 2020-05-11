//
// Created by Martin Blicha on 10.05.20.
//

#ifndef OPENSMT_RDLTHANDLER_H
#define OPENSMT_RDLTHANDLER_H

#include "TSolverHandler.h"

class STPSolver;
class LRALogic;

class RDLTHandler : public TSolverHandler
{
private:
    LRALogic& logic;
    STPSolver *stpsolver;
public:
    RDLTHandler(SMTConfig& c, LRALogic& l, vec<DedElem>& d, TermMapper& tmap);
    virtual ~RDLTHandler() = default;
    virtual void fillTmpDeds(PTRef root, Map<PTRef,int,PTRefHash> &refs) override;
    virtual bool assertLit_special(PtAsgn) override;
    virtual Logic& getLogic() override;
    virtual const Logic& getLogic() const override;
//    virtual lbool getPolaritySuggestion(PTRef) const override;

};


#endif //OPENSMT_RDLTHANDLER_H
