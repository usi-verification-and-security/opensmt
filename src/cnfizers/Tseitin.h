/*
* Copyright (c) 2008-2012, Roberto Bruttomesso
* Copyright (c) 2012-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
* Copyright (c) 2022-2023, Martin Blicha <martin.blicha@gmail.com>
*
*  SPDX-License-Identifier: MIT
*
*/

#ifndef TSEITIN_H
#define TSEITIN_H

#include "PTRef.h"
#include "Cnfizer.h"

class Tseitin : public Cnfizer
{
public:
    Tseitin(Logic & logic, TermMapper & tmap)
        : Cnfizer(logic, tmap) {}

private:

    // Cache of already cnfized terms. Note that this is different from Cnfizer cache of already processed top-level flas
    Cache alreadyCnfized;

    void cnfize(PTRef) override;  // Cnfize the given term
    void cnfizeAnd(PTRef);        // Cnfize conjunctions
    void cnfizeOr(PTRef);         // Cnfize disjunctions
    void cnfizeIff(PTRef);        // Cnfize iffs
    void cnfizeXor(PTRef);        // Cnfize xors
    void cnfizeIfthenelse(PTRef); // Cnfize if then elses
    void cnfizeImplies(PTRef);    // Cnfize implications
};

#endif
