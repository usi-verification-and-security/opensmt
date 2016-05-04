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
    //assert( config.produce_inter() == 0 || partitions != 0 );
#endif

    assert(formula != PTRef_Undef);
    // Top level formula must not be and anymore
    assert(!logic.isAnd(formula));

    // Add the top level literal as a unit to solver.
    if (!logic.isOr(formula)) {
        vec<Lit> clause;
        clause.push(findLit(formula));
#ifdef PRODUCE_PROOF
//        if (config.produce_inter() != 0)
  //          addClause(clause, partitions);
#endif
        addClause( clause );
    }
    vec<PTRef> unprocessed_terms;       // Stack for unprocessed terms
    unprocessed_terms.push(formula);    // Start with this term
    Map<PTRef,bool,PTRefHash,Equal<PTRef> >   processed;  // Is a term already processed
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
        SymRef symb = logic.getPterm(ptr).symb();
        int sz = logic.getPterm(ptr).size();
        bool need_def = (ptr == formula ? false : true); // Definition variable not needed for top formula
        if (logic.isAnd(ptr))
            cnfizeAnd(ptr);
        else if (logic.isOr(ptr))
#ifdef PRODUCE_PROOF
            cnfizeOr(ptr, 0, need_def); //FIXME
#else
            cnfizeOr(ptr, need_def);
#endif
        else if (logic.isXor(ptr))
            cnfizeXor(ptr);
        else if (logic.isIff(ptr))
            cnfizeIff(ptr);
        else if (logic.isImplies(ptr))
            cnfizeImplies(ptr);
        else if (logic.isDistinct(ptr))
            cnfizeDistinct(ptr);
        else if (logic.isIte(ptr))
            cnfizeIfthenelse(ptr);
        else if (!logic.isNot(ptr) && sz > 0) {
            // XXX Cnfize equalities here
            if (logic.isEquality(ptr)) {
                goto tseitin_end;
                // This is a bridge equality
                // It should be treated as a literal by the SAT solver
            }
            if (logic.isDisequality(ptr) || (logic.lookupUPEq(ptr) != PTRef_Undef) ) {
                // Uninterpreted predicate.  Special handling
                goto tseitin_end;
            }
            else {
                opensmt_error2("operator not handled", logic.getSymName(ptr));
            }
        }

        {
            Pterm& pt = logic.getPterm(ptr);
            for (int i = 0; i < pt.size(); i++)
                unprocessed_terms.push(pt[i]); // Using the PTRef is safe if a reallocation happened
        }
tseitin_end:
        if (need_def) // Only mark as processed if the definition is formed
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
    for (int i = 0; i < logic.getPterm(and_term).size(); i++) {
        PTRef arg = logic.getPterm(and_term)[i];
        little_clause.push( findLit(arg) );
        big_clause   .push(~findLit(arg));
#ifdef PRODUCE_PROOF
//        if ( config.produce_inter > 0 )
  //          addClause( little_clause, partitions );
    //    else
#endif
            addClause(little_clause);        // Adds a little clause to the solver
        little_clause.pop();
    }
#ifdef PRODUCE_PROOF
//    if ( config.produce_inter > 0 )
  //      addClause( big_clause, partitions );
    //else
#endif
        addClause( big_clause );                    // Adds a big clause to the solver
}

void Tseitin::cnfizeOr( PTRef or_term
#ifdef PRODUCE_PROOF
                      , const ipartitions_t partitions
#endif
                      , bool def)
{
    if (!def) {
        vec<Lit> big_clause;
        for (int i = 0 ; i < logic.getPterm(or_term).size(); i++)
            big_clause.push(findLit(logic.getPterm(or_term)[i]));

        addClause(big_clause);
        return;
    }
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
    for (int i = 0 ; i < logic.getPterm(or_term).size(); i++) {
        Lit arg = findLit(logic.getPterm(or_term)[i]);
        little_clause.push(~arg);
        big_clause   .push( arg);
#ifdef PRODUCE_PROOF
//        if ( config.produce_inter > 0 )
  //          addClause( little_clause, partitions );
    //    else
#endif
            addClause(little_clause);        // Adds a little clause to the solver
        little_clause.pop();
    }
#ifdef PRODUCE_PROOF
//    if (config.produce_inter > 0)
  //      addClause( big_clause, partitions );
    //else
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

    Lit arg0 = findLit(logic.getPterm(xor_term)[0]);
    Lit arg1 = findLit(logic.getPterm(xor_term)[1]);
    vec<Lit> clause;

    clause.push(~v);

    // First clause
    clause.push(arg0);
    clause.push(arg1);
#ifdef PRODUCE_PROOF
//    if (config.produce_inter > 0)
  //      addClause(clause, partitions);
    //else
#endif
        addClause(clause); // Adds a little clause to the solver
    clause.pop();
    clause.pop();

    // Second clause
    clause.push(~arg0);
    clause.push(~arg1);
#ifdef PRODUCE_PROOF
//    if (config.produce_inter > 0)
  //      addClause(clause, partitions);
    //else
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
//    if (config.produce_inter > 0)
  //      addClause(clause, partitions);
    //else
#endif
        addClause(clause); // Adds a little clause to the solver
    clause.pop();
    clause.pop();

    // Fourth clause
    clause.push( arg0);
    clause.push(~arg1);
#ifdef PRODUCE_PROOF
//    if (config.produce_inter > 0)
  //      addClause(clause, partitions);
    //else
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
    assert(logic.getPterm(eq_term).size() == 2);
    Lit v = findLit(eq_term);
    Lit arg0 = findLit(logic.getPterm(eq_term)[0]);
    Lit arg1 = findLit(logic.getPterm(eq_term)[1]);
    vec<Lit> clause;

    clause.push(~v);

    // First clause
    clause.push( arg0);
    clause.push(~arg1);
#ifdef PRODUCE_PROOF
//    if (config.produce_inter > 0)
  //      addClause(clause, partitions);
    //else
#endif
        addClause(clause);           // Adds a little clause to the solver

    clause.pop();
    clause.pop();

    // Second clause
    clause.push(~arg0);
    clause.push( arg1);
#ifdef PRODUCE_PROOF
//    if (config.produce_inter > 0)
  //      addClause(clause, partitions);
    //else
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
//    if ( config.produce_inter > 0 )
  //      addClause(clause, partitions);
    //else
#endif
        addClause(clause);           // Adds a little clause to the solver
    clause.pop();
    clause.pop();

    // Fourth clause
    clause.push(~arg0);
    clause.push(~arg1);
#ifdef PRODUCE_PROOF
//    if (config.produce_inter > 0)
  //      addClause(clause, partitions);
    //else
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
    Pterm& pt_ite = logic.getPterm(ite_term);
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

    Pterm& pt_impl = logic.getPterm(impl_term);
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


// TODO: This does not seem to be the right implementation...
void Tseitin::cnfizeDistinct( PTRef distinct_term
#ifdef PRODUCE_PROOF
                              , const ipartitions_t partitions
#endif
                              )
{
    cnfizeXor(distinct_term);
}

void Tseitin::copyArgsWithCache(PTRef tr, vec<PTRef>& args, Map<PTRef, PTRef, PTRefHash>& cache)
{
    Pterm& t = logic.getPterm(tr);
    for (int i = 0; i < t.size(); i++) {
        if (cache.contains(t[i]))
            args.push(cache[t[i]]);
        else
            args.push(t[i]);
    }
}
