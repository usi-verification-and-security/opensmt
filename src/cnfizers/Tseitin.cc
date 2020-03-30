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


bool Tseitin::cnfize(PTRef formula) {
    assert(formula != PTRef_Undef);
    // Top level formula must not be and anymore
    assert(!logic.isAnd(formula));
    bool res = true;
    // Add the top level literal as a unit to solver.
    if (!logic.isOr(formula)) {
        vec<Lit> clause;
        clause.push(this->getOrCreateLiteralFor(formula));
        res &= addClause(clause);
    }

    vec<PTRef> unprocessed_terms;       // Stack for unprocessed terms
    unprocessed_terms.push(formula);    // Start with this term
    res = declare(unprocessed_terms, formula);
    return res;
}

bool Tseitin::declare(vec<PTRef>& unprocessed_terms, PTRef formula) {
    bool res = true;
    Map<PTRef,bool,PTRefHash,Equal<PTRef>> processed;  // Is a term already processed

    //
    // Visit the DAG of the formula
    //
    while (unprocessed_terms.size() != 0) {

        PTRef ptr = unprocessed_terms.last();
        unprocessed_terms.pop();
        //
        // Skip if the node has already been processed before
        //
        if (processed.has(ptr))
            continue;

        // Here (after the checks) not safe to use Pterm& since cnfize.* can alter the table of terms
        // by calling findLit
        int sz = logic.getPterm(ptr).size();
        bool need_def = (ptr == formula ? false : true); // Definition variable not needed for top formula
        if (logic.isAnd(ptr))
            res &= cnfizeAnd(ptr);
        else if (logic.isOr(ptr))
            res &= cnfizeOr(ptr, need_def);
        else if (logic.isXor(ptr))
            res &= cnfizeXor(ptr);
        else if (logic.isIff(ptr))
            res &= cnfizeIff(ptr);
        else if (logic.isImplies(ptr))
            res &= cnfizeImplies(ptr);
        else if (logic.isIte(ptr))
            res &= cnfizeIfthenelse(ptr);
        else if (!logic.isNot(ptr) && sz > 0) {
            goto tseitin_end;
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

    return res;
}


bool Tseitin::cnfizeAnd(PTRef and_term)
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
    Lit v = this->getOrCreateLiteralFor(and_term);
    vec<Lit> little_clause;
    vec<Lit> big_clause;
    int size = logic.getPterm(and_term).size();
    big_clause.capacity(size + 1);
    little_clause.push(~v);
    big_clause   .push(v);
    bool res = true;
    for (int i = 0; i < size; i++) {
        PTRef arg = logic.getPterm(and_term)[i];
        little_clause.push( this->getOrCreateLiteralFor(arg) );
        big_clause   .push(~this->getOrCreateLiteralFor(arg));
        res &= addClause(little_clause);        // Adds a little clause to the solver
        little_clause.pop();
    }
    res &= addClause(big_clause);                    // Adds a big clause to the solver
    return res;
}



bool Tseitin::cnfizeOr(PTRef or_term, bool def)
{
    if (!def) {
        vec<Lit> big_clause;
        for (int i = 0 ; i < logic.getPterm(or_term).size(); i++)
            big_clause.push(this->getOrCreateLiteralFor(logic.getPterm(or_term)[i]));

        return addClause(big_clause);
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
    Lit v = this->getOrCreateLiteralFor(or_term);
    little_clause.push( v);
    big_clause   .push(~v);
    bool res = true;
    for (int i = 0 ; i < logic.getPterm(or_term).size(); i++) {
        Lit arg = this->getOrCreateLiteralFor(logic.getPterm(or_term)[i]);
        little_clause.push(~arg);
        big_clause   .push( arg);

        res &= addClause(little_clause);        // Adds a little clause to the solver

        little_clause.pop();
    }
    res &= addClause(big_clause);                    // Adds a big clause to the solver
    return res;
}


bool Tseitin::cnfizeXor(PTRef xor_term)
{
    //
    // ( a_0 xor a_1 )
    //
    // <=>
    //
    // aux = ( -aux | a_0  | a_1 ) & ( -aux | -a_0 | -a_1 ) &
    //       (  aux | -a_0 | a_1 ) & (  aux |  a_0 | -a_1 )
    //

    Lit v = this->getOrCreateLiteralFor(xor_term);

    Lit arg0 = this->getOrCreateLiteralFor(logic.getPterm(xor_term)[0]);
    Lit arg1 = this->getOrCreateLiteralFor(logic.getPterm(xor_term)[1]);
    vec<Lit> clause;
    bool res = true;

    clause.push(~v);

    // First clause
    clause.push(arg0);
    clause.push(arg1);

    res &= addClause(clause);
    clause.pop();
    clause.pop();

    // Second clause
    clause.push(~arg0);
    clause.push(~arg1);

    res &= addClause(clause);
    clause.pop();
    clause.pop();

    clause.pop();
    clause.push(v);

    // Third clause
    clause.push(~arg0);
    clause.push( arg1);

    res &= addClause(clause);

    clause.pop();
    clause.pop();

    // Fourth clause
    clause.push( arg0);
    clause.push(~arg1);

    res &= addClause(clause);
    return res;
}

bool Tseitin::cnfizeIff(PTRef eq_term)
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
    Lit v = this->getOrCreateLiteralFor(eq_term);
    Lit arg0 = this->getOrCreateLiteralFor(logic.getPterm(eq_term)[0]);
    Lit arg1 = this->getOrCreateLiteralFor(logic.getPterm(eq_term)[1]);
    vec<Lit> clause;
    bool res = true;

    clause.push(~v);

    // First clause
    clause.push( arg0);
    clause.push(~arg1);

    res &= addClause(clause);

    clause.pop();
    clause.pop();

    // Second clause
    clause.push(~arg0);
    clause.push( arg1);

    res &= addClause(clause);

    clause.pop();
    clause.pop();

    clause.pop();
    clause.push(v);

    // Third clause
    clause.push(arg0);
    clause.push(arg1);

    res &= addClause(clause);

    clause.pop();
    clause.pop();

    // Fourth clause
    clause.push(~arg0);
    clause.push(~arg1);

    res &= addClause(clause);
    return res;
}


bool Tseitin::cnfizeIfthenelse(PTRef ite_term)
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

    Lit v  = this->getOrCreateLiteralFor(ite_term);
    Lit a0 = this->getOrCreateLiteralFor(pt_ite[0]);
    Lit a1 = this->getOrCreateLiteralFor(pt_ite[1]);
    Lit a2 = this->getOrCreateLiteralFor(pt_ite[2]);

    vec<Lit> clause;
    bool res = true;

    clause.push(~v); clause.push(~a0); clause.push(a1);

    res &= addClause(clause);

    clause.clear();

    clause.push(~v); clause.push(a0); clause.push(a2);
    res &= addClause(clause);
    clause.clear();

    clause.push(v); clause.push(~a0); clause.push(~a1);
    res &= addClause(clause);
    clause.clear();

    clause.push(v); clause.push(a0); clause.push(~a2);
    res &= addClause(clause);
    return res;
}


bool Tseitin::cnfizeImplies(PTRef impl_term)
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

    Lit v  = this->getOrCreateLiteralFor(impl_term);
    Lit a0 = this->getOrCreateLiteralFor(pt_impl[0]);
    Lit a1 = this->getOrCreateLiteralFor(pt_impl[1]);

    vec<Lit> clause;
    bool res = true;

    clause.push(v);

    clause.push(a0);

    res &= addClause(clause);

    clause.pop();

    clause.push(~a1);

    res &= addClause(clause);

    clause.clear();

    clause.push(~v); clause.push(~a0); clause.push(a1);

    res &= addClause(clause);
    return res;
}

//void Tseitin::copyArgsWithCache(PTRef tr, vec<PTRef>& args, Map<PTRef, PTRef, PTRefHash>& cache)
//{
//    Pterm& t = logic.getPterm(tr);
//    for (int i = 0; i < t.size(); i++) {
//        if (cache.has(t[i]))
//            args.push(cache[t[i]]);
//        else
//            args.push(t[i]);
//    }
//}
