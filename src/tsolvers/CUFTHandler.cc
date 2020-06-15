#include "CUFTHandler.h"
#include "CUFLogic.h"

CUFTHandler::CUFTHandler(SMTConfig & c, CUFLogic & l, TermMapper & tmap)
    : UFTHandler(c, l, tmap)
    , logic(l)
{}

CUFTHandler::~CUFTHandler()
{}

CUFLogic&
CUFTHandler::getLogic()
{
    return logic;
}
