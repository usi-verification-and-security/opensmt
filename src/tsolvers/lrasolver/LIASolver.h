
#ifndef LIASOLVER_H
#define LIASOLVER_H

#include "TSolver.h"
#include "LIALogic.h"
#include "LRALogic.C"



class LIASolver : public TSolver
{
public:
    LIASolver ( SMTConfig &
            , LIALogic&
            , vec<DedElem> & );
    ~LIASolver ( );


private:

    LIALogic&    logic;


};

#endif

