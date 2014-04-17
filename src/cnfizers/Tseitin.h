/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
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

    Tseitin( PtStore&       ptstore_
           , SMTConfig&     config_
           , SymStore&      symstore_
           , SStore&        sstore_
           , Logic&         logic_
           , TermMapper&    tmap_
           , THandler&      thandler_
           , SimpSMTSolver& solver_
           )
      : Cnfizer(ptstore_
                , config_
                , symstore_
                , sstore_
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
    void cnfizeOr         (PTRef);                          // Cnfize disjunctions
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
