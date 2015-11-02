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

#ifdef ENABLE_SHARING_BUG
    bool cnfize         (PTRef, Map<PTRef, PTRef, PTRefHash>& valdupmap);
#else
    bool cnfize          ( PTRef
#ifdef PRODUCE_PROOF
                          , const ipartitions_t = 0 
#endif
                          );            // Do the actual cnfization
#endif
#ifdef PRODUCE_PROOF
    void cnfizeAnd        ( Enode *, Enode *, const ipartitions_t = 0 ); // Cnfize conjunctions
    void cnfizeOr         ( Enode *, Enode *, const ipartitions_t = 0 ); // Cnfize disjunctions
    void cnfizeIff        ( Enode *, Enode *, const ipartitions_t = 0 ); // Cnfize iffs
    void cnfizeXor        ( Enode *, Enode *, const ipartitions_t = 0 ); // Cnfize xors
    void cnfizeIfthenelse ( Enode *, Enode *, const ipartitions_t = 0 ); // Cnfize if then elses
#else // PRODUCE_PROOF
#ifdef ENABLE_SHARING_BUG
    void cnfizeAnd        (vec<PTRef>&, PTRef);             // Cnfize conjunctions
    void cnfizeOr         (vec<PTRef>&, PTRef);             // Cnfize disjunctions
    void cnfizeIff        (vec<PTRef>&, PTRef);             // Cnfize iffs
    void cnfizeXor        (vec<PTRef>&, PTRef);             // Cnfize xors
    void cnfizeIfthenelse (vec<PTRef>&, PTRef);             // Cnfize if then elses
    void cnfizeImplies    (vec<PTRef>&, PTRef);             // Cnfize if then elses
    void cnfizeDistinct   (vec<PTRef>&, PTRef);             // Cnfize distinctions
#else // ENABLE_SHARING_BUG
    void cnfizeAnd        (PTRef);                          // Cnfize conjunctions
    void cnfizeOr         (PTRef, bool def=true);           // Cnfize disjunctions
    void cnfizeIff        (PTRef);                          // Cnfize iffs
    void cnfizeXor        (PTRef);                          // Cnfize xors
    void cnfizeIfthenelse (PTRef);                          // Cnfize if then elses
    void cnfizeImplies    (PTRef);                          // Cnfize if then elses
    void cnfizeDistinct   (PTRef);                          // Cnfize distinctions
#endif // ENABLE_SHARING_BUG
#endif // PRODUCE_PROOF
    void copyArgsWithCache(PTRef, vec<PTRef>&, Map<PTRef, PTRef, PTRefHash>&);
};

#endif
