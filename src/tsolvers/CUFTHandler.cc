#include "CUFTHandler.h"
#include "CUFLogic.h"

CUFTHandler::CUFTHandler(SMTConfig & c, CUFLogic & l)
    : UFTHandler(c, l)
    , logic(l)
{}

CUFTHandler::~CUFTHandler()
{}

CUFLogic&
CUFTHandler::getLogic()
{
    return logic;
}
