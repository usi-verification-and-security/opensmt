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

    Tseitin(PtStore&   ptstore_,
            SMTSolver& solver_,
            SMTConfig& config_,
            TStore&    symstore_,
            SStore&    sstore_,
            TRef       sym_and,
            TRef       sym_or,
            TRef       sym_not,
            TRef       sym_eq,
            SRef       sort_bool
           )
      : Cnfizer(ptstore_, solver_, config_, symstore_, sstore_, sym_and, sym_or, sym_not, sym_eq, sort_bool)
    {}

    ~Tseitin( ) { }

private:

    Map<PTRef,Var,PTRefHash,Equal<PTRef> > processed;

    bool cnfize           ( PTRef
#ifdef PRODUCE_PROOF
                          , const ipartitions_t = 0 
#endif
                          );            // Do the actual cnfization
#ifdef PRODUCE_PROOF
//  void cnfizeAnd        ( Enode *, Enode *, const ipartitions_t = 0 ); // Cnfize conjunctions
//  void cnfizeOr         ( Enode *, Enode *, const ipartitions_t = 0 ); // Cnfize disjunctions
//  void cnfizeIff        ( Enode *, Enode *, const ipartitions_t = 0 ); // Cnfize iffs
//  void cnfizeXor        ( Enode *, Enode *, const ipartitions_t = 0 ); // Cnfize xors
//  void cnfizeIfthenelse ( Enode *, Enode *, const ipartitions_t = 0 ); // Cnfize if then elses
#else
//  void cnfizeAnd        ( Enode *, Enode * );                          // Cnfize conjunctions
//  void cnfizeOr         ( Enode *, Enode * );                          // Cnfize disjunctions
//  void cnfizeIff        ( Enode *, Enode * );                          // Cnfize iffs
//  void cnfizeXor        ( Enode *, Enode * );                          // Cnfize xors
//  void cnfizeIfthenelse ( Enode *, Enode * );                          // Cnfize if then elses
#endif
};

#endif
