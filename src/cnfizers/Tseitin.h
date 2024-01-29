/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#ifndef TSEITIN_H
#define TSEITIN_H

#include "PTRef.h"
#include "Cnfizer.h"

class Tseitin : public Cnfizer
{
public:

    Tseitin( SMTConfig&     config_
           , Logic&         logic_
           , PartitionManager &pmanager_
           , TermMapper&    tmap_
           , SimpSMTSolver& solver_
           )
      : Cnfizer( config_
                , logic_
                , pmanager_
                , tmap_
                , solver_ )
        , alreadyCnfized(logic_.getTerm_true())
      {}

private:

    // Cache of already cnfized terms. Note that this is different from Cnfizer cache of already processed top-level flas
    Cache alreadyCnfized;

    bool cnfize             (PTRef);                          // Cnfize the given term
    bool cnfizeAnd          (PTRef);                          // Cnfize conjunctions
    bool cnfizeOr           (PTRef);                          // Cnfize disjunctions
    bool cnfizeIff          (PTRef);                          // Cnfize iffs
    bool cnfizeXor          (PTRef);                          // Cnfize xors
    bool cnfizeIfthenelse   (PTRef);                          // Cnfize if then elses
    bool cnfizeImplies      (PTRef);                          // Cnfize if then elses
//    void copyArgsWithCache(PTRef, vec<PTRef>&, Map<PTRef, PTRef, PTRefHash>&);
};

#endif
