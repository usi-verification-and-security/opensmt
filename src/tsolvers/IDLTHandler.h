//
// Created by Martin Blicha on 10.05.20.
//

#ifndef OPENSMT_IDLTHANDLER_H
#define OPENSMT_IDLTHANDLER_H

#include "TSolverHandler.h"

class STPSolver;
class LIALogic;

class IDLTHandler : public TSolverHandler
{
private:
    LIALogic& logic;
    STPSolver *stpsolver;
public:
    IDLTHandler(SMTConfig& c, LIALogic& l, vec<DedElem>& d, TermMapper& tmap);
    virtual ~IDLTHandler() = default;
    virtual void fillTmpDeds(PTRef root, Map<PTRef,int,PTRefHash> &refs) override;
    virtual bool assertLit_special(PtAsgn) override;
    virtual Logic& getLogic() override;
    virtual const Logic& getLogic() const override;
//    virtual lbool getPolaritySuggestion(PTRef) const override;

};


#endif //OPENSMT_IDLTHANDLER_H
