/*
 * Copyright (c) 2008-2012, Roberto Bruttomesso
 * Copyright (c) 2012-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022-2023, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "Tseitin.h"

namespace opensmt {
void Tseitin::cnfize(PTRef term) {
    vec<PTRef> unprocessed_terms{term};

    // Visit the DAG of the formula
    while (unprocessed_terms.size() != 0) {
        PTRef ptr = unprocessed_terms.last();
        unprocessed_terms.pop();
        // Skip if the node has already been processed before
        if (alreadyCnfized.contains(ptr, currentFrameId)) { continue; }

        // Here (after the checks) not safe to use Pterm& since cnfize.* can alter the table of terms
        // by calling findLit
        int sz = logic.getPterm(ptr).size();
        if (logic.isAnd(ptr))
            cnfizeAnd(ptr);
        else if (logic.isOr(ptr))
            cnfizeOr(ptr);
        else if (logic.isXor(ptr))
            cnfizeXor(ptr);
        else if (logic.isIff(ptr))
            cnfizeIff(ptr);
        else if (logic.isImplies(ptr))
            cnfizeImplies(ptr);
        // Ites are handled through the ite manager system and treated here as variables
        //        else if (logic.isIte(ptr))
        //            res &= cnfizeIfthenelse(ptr);
        else if (!logic.isNot(ptr) && sz > 0) { // do not recurse into atoms
            goto tseitin_end;
        }
        for (PTRef child : logic.getPterm(ptr)) {
            unprocessed_terms.push(child);
        }
    tseitin_end:
        alreadyCnfized.insert(ptr, currentFrameId);
    }
}

void Tseitin::cnfizeAnd(PTRef and_term) {
    // ( a_0 & ... & a_{n-1} )
    // <=>
    // aux = ( -aux | a_0 ) & ... & ( -aux | a_{n-1} ) & ( aux & -a_0 & ... & -a_{n-1} )
    Lit v = this->getOrCreateLiteralFor(and_term);
    vec<Lit> big_clause;
    int size = logic.getPterm(and_term).size();
    big_clause.capacity(size + 1);
    big_clause.push(v);
    for (int i = 0; i < size; ++i) {
        PTRef arg = logic.getPterm(and_term)[i];
        Lit argLit = this->getOrCreateLiteralFor(arg);
        big_clause.push(~argLit);
        addClause({~v, argLit});
    }
    addClause(std::move(big_clause));
}

void Tseitin::cnfizeOr(PTRef or_term) {
    // ( a_0 | ... | a_{n-1} )
    // <=>
    // aux = ( aux | -a_0 ) & ... & ( aux | -a_{n-1} ) & ( -aux | a_0 | ... | a_{n-1} )
    Lit v = this->getOrCreateLiteralFor(or_term);
    vec<Lit> big_clause;
    int size = logic.getPterm(or_term).size();
    big_clause.push(~v);
    for (int i = 0; i < size; ++i) {
        PTRef arg = logic.getPterm(or_term)[i];
        Lit argLit = this->getOrCreateLiteralFor(arg);
        big_clause.push(argLit);
        addClause({v, ~argLit});
    }
    addClause(std::move(big_clause));
}

void Tseitin::cnfizeXor(PTRef xor_term) {
    // ( a_0 xor a_1 )
    // <=>
    // aux = ( -aux | a_0  | a_1 ) & ( -aux | -a_0 | -a_1 ) &
    //       (  aux | -a_0 | a_1 ) & (  aux |  a_0 | -a_1 )

    Lit v = this->getOrCreateLiteralFor(xor_term);
    Lit arg0 = this->getOrCreateLiteralFor(logic.getPterm(xor_term)[0]);
    Lit arg1 = this->getOrCreateLiteralFor(logic.getPterm(xor_term)[1]);

    // First clause
    addClause({~v, arg0, arg1});
    // Second clause
    addClause({~v, ~arg0, ~arg1});
    // Third clause
    addClause({v, ~arg0, arg1});
    // Fourth clause
    addClause({v, arg0, ~arg1});
}

void Tseitin::cnfizeIff(PTRef eq_term) {
    // ( a_0 <-> a_1 )
    // <=>
    // aux = ( -aux |  a_0 | -a_1 ) & ( -aux | -a_0 |  a_1 ) &
    //       (  aux |  a_0 |  a_1 ) & (  aux | -a_0 | -a_1 )
    assert(logic.getPterm(eq_term).size() == 2);
    Lit v = this->getOrCreateLiteralFor(eq_term);
    Lit arg0 = this->getOrCreateLiteralFor(logic.getPterm(eq_term)[0]);
    Lit arg1 = this->getOrCreateLiteralFor(logic.getPterm(eq_term)[1]);

    // First clause
    addClause({~v, arg0, ~arg1});
    // Second clause
    addClause({~v, ~arg0, arg1});
    // Third clause
    addClause({v, arg0, arg1});
    // Fourth clause
    addClause({v, ~arg0, ~arg1});
}

void Tseitin::cnfizeIfthenelse(PTRef ite_term) {
    //  (!a | !i | t) & (!a | i | e) & (a | !i | !t) & (a | i | !e)
    // ( if a_0 then a_1 else a_2 )
    // <=>
    // aux = ( -aux | -a_0 |  a_1 ) &
    //       ( -aux |  a_0 |  a_2 ) &
    //       (  aux | -a_0 | -a_1 ) &
    //       (  aux |  a_0 | -a_2 )
    assert(logic.getPterm(ite_term).size() == 3);
    Lit v = this->getOrCreateLiteralFor(ite_term);
    Lit a0 = this->getOrCreateLiteralFor(logic.getPterm(ite_term)[0]);
    Lit a1 = this->getOrCreateLiteralFor(logic.getPterm(ite_term)[1]);
    Lit a2 = this->getOrCreateLiteralFor(logic.getPterm(ite_term)[2]);

    addClause({~v, ~a0, a1});
    addClause({~v, a0, a2});
    addClause({v, ~a0, ~a1});
    addClause({v, a0, ~a2});
}

void Tseitin::cnfizeImplies(PTRef impl_term) {
    // ( a_0 => a_1 )
    // <=>
    // aux = ( -aux | -a_0 |  a_1 ) &
    //       (  aux |  a_0 )        &
    //       (  aux | -a_1 )
    assert(logic.getPterm(impl_term).size() == 2);
    Lit v = this->getOrCreateLiteralFor(impl_term);
    Lit a0 = this->getOrCreateLiteralFor(logic.getPterm(impl_term)[0]);
    Lit a1 = this->getOrCreateLiteralFor(logic.getPterm(impl_term)[1]);

    addClause({v, a0});
    addClause({v, ~a1});
    addClause({~v, ~a0, a1});
}

} // namespace opensmt
