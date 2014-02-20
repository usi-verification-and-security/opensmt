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

#include "Cnfizer.h"
#include "Tseitin.h"

//
// Performs the actual cnfization
//
bool Tseitin::cnfize(PTRef formula
#ifdef PRODUCE_PROOF
                    , const ipartitions_t partitions
#endif
                    )
{
#ifdef PRODUCE_PROOF
    assert( config.produce_inter == 0 || partitions != 0 );
#endif

    assert(formula != PTRef_Undef);
    Pterm& ft = ptstore[formula];
    // Top level formula must not be and anymore
    assert(ft.symb() != logic.getSym_and());

    // Add the top level literal as a unit to solver.
    vec<Lit> clause;
    clause.push(findLit(formula));
#ifdef PRODUCE_PROOF
    if (config.produce_inter != 0)
        addClause(clause, partitions);
#endif
    addClause( clause );

    vec<PTRef> unprocessed_terms;       // Stack for unprocessed terms
    unprocessed_terms.push(formula);    // Start with this term
    //
    // Visit the DAG of the formula
    //
    while (unprocessed_terms.size() != 0) {
        PTRef ptr = unprocessed_terms.last();
        unprocessed_terms.pop();
        //
        // Skip if the node has already been processed before
        //
        if (processed.contains(ptr))
            continue;

        // Here (after the checks) not safe to use Pterm& since cnfize.* can alter the table of terms
        // by calling findLit
        SymRef symb = ptstore[ptr].symb();
        int sz = ptstore[ptr].size();
        if (symb == logic.getSym_and())
            cnfizeAnd(ptr);
        else if (symb == logic.getSym_or())
            cnfizeOr(ptr);
        else if (symb == logic.getSym_xor())
            cnfizeXor(ptr);
        else if (symb == logic.getSym_eq())
            cnfizeIff(ptr);
        else if (symb == logic.getSym_implies())
            cnfizeImplies(ptr);
        else if (symb == logic.getSym_distinct())
            cnfizeDistinct(ptr);
        else if (symb == logic.getSym_ite())
            cnfizeIfthenelse(ptr);
        else if (symb != logic.getSym_not() && sz > 0) {
            // XXX Cnfize equalities here
            if (logic.isEquality(symb)) {
                goto tseitin_end;
                // This is a bridge equality
                // It should be treated as a literal by the SAT solver
            }
            if (logic.lookupUPEq(ptr) != PTRef_Undef) {
                // Uninterpreted predicate.  Special handling
                goto tseitin_end;
            }
            else {
                opensmt_error2("operator not handled", symstore.getName(ptstore[ptr].symb()));
            }
        }

        {
            Pterm& pt = ptstore[ptr];
            for (int i = 0; i < pt.size(); i++)
                unprocessed_terms.push(pt[i]); // It would seem that using the reference is not safe if a reallocation happened?
        }
tseitin_end:
        processed.insert(ptr, true);

    }

    return true;
}


void Tseitin::cnfizeAnd( PTRef and_term
#ifdef PRODUCE_PROOF
                       , const ipartitions_t partitions
#endif
                       )
{
//  assert( list );
//  assert( list->isList( ) );
    //
    // ( a_0 & ... & a_{n-1} )
    //
    // <=>
    //
    // aux = ( -aux | a_0 ) & ... & ( -aux | a_{n-1} ) & ( aux & -a_0 & ... & -a_{n-1} )
    //
    Lit v = findLit(and_term);
    vec<Lit> little_clause;
    vec<Lit> big_clause;
    little_clause.push(~v);
    big_clause   .push(v);
    for (int i = 0; i < ptstore[and_term].size(); i++) {
        PTRef arg = ptstore[and_term][i];
        little_clause.push( findLit(arg) );
        big_clause   .push(~findLit(arg));
#ifdef PRODUCE_PROOF
        if ( config.produce_inter > 0 )
            addClause( little_clause, partitions );
        else
#endif
            addClause(little_clause);        // Adds a little clause to the solver
        little_clause.pop();
    }
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
        addClause( big_clause, partitions );
    else
#endif
        addClause( big_clause );                    // Adds a big clause to the solver
}

void Tseitin::cnfizeOr( PTRef or_term
#ifdef PRODUCE_PROOF
                      , const ipartitions_t partitions
#endif
                      )
{
//  assert( list );
//  assert( list->isList( ) );
    //
    // ( a_0 | ... | a_{n-1} )
    //
    // <=>
    //
    // aux = ( aux | -a_0 ) & ... & ( aux | -a_{n-1} ) & ( -aux | a_0 | ... | a_{n-1} )
    //
    vec<Lit>    little_clause;
    vec<Lit>    big_clause;
    Lit v = findLit(or_term);
    little_clause.push( v);
    big_clause   .push(~v);
    for (int i = 0 ; i < ptstore[or_term].size(); i++) {
        Lit arg = findLit(ptstore[or_term][i]);
        little_clause.push(~arg);
        big_clause   .push( arg);
#ifdef PRODUCE_PROOF
        if ( config.produce_inter > 0 )
            addClause( little_clause, partitions );
        else
#endif
            addClause(little_clause);        // Adds a little clause to the solver
        little_clause.pop();
    }
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        addClause( big_clause, partitions );
    else
#endif
            addClause(big_clause);                    // Adds a big clause to the solver
}

void Tseitin::cnfizeXor(PTRef xor_term
#ifdef PRODUCE_PROOF
                       , const ipartitions_t partitions
#endif
                       )
{
    //
    // ( a_0 xor a_1 )
    //
    // <=>
    //
    // aux = ( -aux | a_0  | a_1 ) & ( -aux | -a_0 | -a_1 ) &
    //       (  aux | -a_0 | a_1 ) & (  aux |  a_0 | -a_1 )
    //

    Lit v = findLit(xor_term);

    Lit arg0 = findLit(ptstore[xor_term][0]);
    Lit arg1 = findLit(ptstore[xor_term][1]);
    vec<Lit> clause;

    clause.push(~v);

    // First clause
    clause.push(arg0);
    clause.push(arg1);
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        addClause(clause, partitions);
    else
#endif
        addClause(clause); // Adds a little clause to the solver
    clause.pop();
    clause.pop();

    // Second clause
    clause.push(~arg0);
    clause.push(~arg1);
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        addClause(clause, partitions);
    else
#endif
        addClause(clause); // Adds a little clause to the solver
    clause.pop();
    clause.pop();

    clause.pop();
    clause.push(v);

    // Third clause
    clause.push(~arg0);
    clause.push( arg1);
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        addClause(clause, partitions);
    else
#endif
        addClause(clause); // Adds a little clause to the solver
    clause.pop();
    clause.pop();

    // Fourth clause
    clause.push( arg0);
    clause.push(~arg1);
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        addClause(clause, partitions);
    else
#endif
        addClause(clause);           // Adds a little clause to the solver
}

void Tseitin::cnfizeIff( PTRef eq_term
#ifdef PRODUCE_PROOF
                       , const ipartitions_t partitions
#endif
                       )
{

    //
    // ( a_0 <-> a_1 )
    //
    // <=>
    //
    // aux = ( -aux |  a_0 | -a_1 ) & ( -aux | -a_0 |  a_1 ) &
    //       (  aux |  a_0 |  a_1 ) & (  aux | -a_0 | -a_1 )
    //
    assert(ptstore[eq_term].size() == 2);
    Lit v = findLit(eq_term);
    Lit arg0 = findLit(ptstore[eq_term][0]);
    Lit arg1 = findLit(ptstore[eq_term][1]);
    vec<Lit> clause;

    clause.push(~v);

    // First clause
    clause.push( arg0);
    clause.push(~arg1);
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        addClause(clause, partitions);
    else
#endif
        addClause(clause);           // Adds a little clause to the solver

    clause.pop();
    clause.pop();

    // Second clause
    clause.push(~arg0);
    clause.push( arg1);
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        addClause(clause, partitions);
    else
#endif
        addClause(clause);           // Adds a little clause to the solver

    clause.pop();
    clause.pop();

    clause.pop();
    clause.push(v);

    // Third clause
    clause.push(arg0);
    clause.push(arg1);
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
        addClause(clause, partitions);
    else
#endif
        addClause(clause);           // Adds a little clause to the solver
    clause.pop();
    clause.pop();

    // Fourth clause
    clause.push(~arg0);
    clause.push(~arg1);
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        addClause(clause, partitions);
    else
#endif
        addClause(clause);           // Adds a little clause to the solver
}

void Tseitin::cnfizeIfthenelse( PTRef ite_term
#ifdef PRODUCE_PROOF
                              , const ipartitions_t partitions
#endif
                              )
{
    //  (!a | !i | t) & (!a | i | e) & (a | !i | !t) & (a | i | !e)
    //
    // ( if a_0 then a_1 else a_2 )
    //
    // <=>
    //
    // aux = ( -aux | -a_0 |  a_1 ) &
    //       ( -aux |  a_0 |  a_2 ) &
    //       (  aux | -a_0 | -a_1 ) &
    //       (  aux |  a_0 | -a_2 )
    //
    Pterm& pt_ite = ptstore[ite_term];
    assert(pt_ite.size() == 3);

    Lit v  = findLit(ite_term);
    Lit a0 = findLit(pt_ite[0]);
    Lit a1 = findLit(pt_ite[1]);
    Lit a2 = findLit(pt_ite[2]);

    vec<Lit> clause;

    clause.push(~v); clause.push(~a0); clause.push(a1);
    addClause( clause ); clause.clear();

    clause.push(~v); clause.push(a0); clause.push(a2);
    addClause( clause ); clause.clear();

    clause.push(v); clause.push(~a0); clause.push(~a1);
    addClause( clause ); clause.clear();

    clause.push(v); clause.push(a0); clause.push(~a2);
    addClause( clause );
}

void Tseitin::cnfizeImplies( PTRef impl_term
#ifdef PRODUCE_PROOF
                              , const ipartitions_t partitions
#endif
                              )
{
    // ( a_0 => a_1 )
    //
    // <=>
    //
    // aux = ( -aux | -a_0 |  a_1 ) &
    //       (  aux |  a_0 )        &
    //       (  aux | -a_1 )
    //

    Pterm& pt_impl = ptstore[impl_term];
    assert(pt_impl.size() == 2);

    Lit v  = findLit(impl_term);
    Lit a0 = findLit(pt_impl[0]);
    Lit a1 = findLit(pt_impl[1]);

    vec<Lit> clause;

    clause.push(v);

    clause.push(a0);
    addClause(clause); clause.pop();

    clause.push(~a1);
    addClause(clause); clause.clear();

    clause.push(~v); clause.push(~a0); clause.push(a1);
    addClause(clause);
}

void Tseitin::cnfizeDistinct( PTRef distinct_term
#ifdef PRODUCE_PROOF
                              , const ipartitions_t partitions
#endif
                              )
{
    cnfizeOr(distinct_term);
}
