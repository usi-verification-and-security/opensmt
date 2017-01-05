#include "CUFTHandler.h"
#include "CUFLogic.h"

CUFTHandler::CUFTHandler(SMTConfig& c, CUFLogic& l, vec<DedElem>& d, TermMapper& tmap)
    : UFTHandler(c, l, d, tmap)
    , logic(l)
{}

CUFLogic&
CUFTHandler::getLogic()
{
    return logic;
}
