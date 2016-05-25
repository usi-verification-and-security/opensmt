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

#include "Global.h"
//#include "Otl.h"
#include "SMTSolver.h"
//#include "Egraph.h"
#include "PtStore.h"
#include "Cnfizer.h"

class Tseitin : public Cnfizer
{
public:

    Tseitin( SMTConfig&     config_
           , Logic&         logic_
           , TermMapper&    tmap_
           , THandler&      thandler_
           , SimpSMTSolver& solver_
           )
      : Cnfizer( config_
                , logic_
                , tmap_
                , thandler_
                , solver_ )
      {}

    ~Tseitin( ) { }


private:

#ifdef PRODUCE_PROOF
    bool cnfize          ( PTRef, const ipartitions_t & );            // Do the actual cnfization
#else
    bool cnfize          ( PTRef );            // Do the actual cnfization
#endif
#ifdef PRODUCE_PROOF
    void cnfizeAnd        (PTRef, const ipartitions_t&);                          // Cnfize conjunctions
    void cnfizeOr         (PTRef, const ipartitions_t&, bool def=true);           // Cnfize disjunctions
    void cnfizeIff        (PTRef, const ipartitions_t&);                          // Cnfize iffs
    void cnfizeXor        (PTRef, const ipartitions_t&);                          // Cnfize xors
    void cnfizeIfthenelse (PTRef, const ipartitions_t&);                          // Cnfize if then elses
    void cnfizeImplies    (PTRef, const ipartitions_t&);
    void cnfizeDistinct   (PTRef, const ipartitions_t&);
#else // PRODUCE_PROOF
    void cnfizeAnd        (PTRef);                          // Cnfize conjunctions
    void cnfizeOr         (PTRef, bool def=true);           // Cnfize disjunctions
    void cnfizeIff        (PTRef);                          // Cnfize iffs
    void cnfizeXor        (PTRef);                          // Cnfize xors
    void cnfizeIfthenelse (PTRef);                          // Cnfize if then elses
    void cnfizeImplies    (PTRef);                          // Cnfize if then elses
    void cnfizeDistinct   (PTRef);                          // Cnfize distinctions
#endif //PRODUCE_PROOF
    void copyArgsWithCache(PTRef, vec<PTRef>&, Map<PTRef, PTRef, PTRefHash>&);
};

#endif
