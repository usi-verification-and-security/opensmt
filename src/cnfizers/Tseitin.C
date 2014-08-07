/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso

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
#ifdef ENABLE_SHARING_BUG
// Figure out what's the difference between the two maps!
bool Tseitin::cnfize(PTRef f, Map<PTRef, PTRef, PTRefHash>& valdupmap)
{
    if (valdupmap.contains(f)) {
        vec<Lit> clause;
        clause.push(findLit(valdupmap[f]));
#ifdef PRODUCE_PROOF
        if (config.produce_inter != 0)
            return addClause(clause, partitions);
#else
        return addClause(clause);
#endif
    }
    vec<PTRef> queue;
    queue.push(f);

    while (queue.size() != 0) {
        PTRef tr = queue.last();
        if (valdupmap.contains(tr)) {
            queue.pop();
            continue;
        }

        bool unprocessed_children = false;

        Pterm& t = logic.getPterm(tr);
        for (int i = 0; i < t.size(); i++) {
            PTRef argr = t[i];
            if (logic.isBooleanOperator(argr) && !valdupmap.contains(argr)) {
                queue.push(argr);
                unprocessed_children = true;
            } else if (logic.isAtom(argr))
                valdupmap.insert(argr, argr);
        }

        if (unprocessed_children) continue;

        queue.pop();
        PTRef result = PTRef_Undef;

        if (logic.isLit(tr)) result = tr;
        else if (logic.isNot(tr)) {
            PTRef tr_clear;
            bool sgn;
            tmap.getTerm(tr, tr_clear, sgn);
            PTRef arg_def = valdupmap[tr_clear];
            result = logic.mkNot(arg_def);
        } else {
            PTRef arg_def = PTRef_Undef;
            vec<PTRef> new_args;
            copyArgsWithCache(tr, new_args, valdupmap);
            if (f != tr) {
                // The definition variable
                char* def_name;
                asprintf(&def_name, "cnf_%d_%d", logic.getPterm(f).getId(), logic.getPterm(tr).getId());
                arg_def = logic.mkBoolVar(def_name);
#ifdef PRODUCE_PROOF
                if ( config.produce_inter != 0 ) {
                    arg_def.setIPartitions( partitions );
                    egraph.addDefinition( arg_def, enode ); // Fix me
	        }
#endif
            }

            if (logic.isAnd(tr))
#ifndef PRODUCE_PROOF
                cnfizeAnd(new_args, arg_def);
#else
                cnfizeAnd(new_args, arg_def, partitions);
#endif
            else if (logic.isOr(tr))
#ifndef PRODUCE_PROOF
                cnfizeOr(new_args, arg_def);
#else
                cnfizeOr(new_args, arg_def, partitions);
#endif
            else if (logic.isIff(tr))
#ifndef PRODUCE_PROOF
                cnfizeIff(new_args, arg_def);
#else
                cnfizeIff(new_args, arg_def, partitions);
#endif
            else if (logic.isXor(tr))
#ifndef PRODUCE_PROOF
                cnfizeXor(new_args, arg_def);
#else
                cnfizeXor(new_args, arg_def, partitions);
#endif
            else if (logic.isImplies(tr))
#ifndef PRODUCE_PROOF
                cnfizeImplies(new_args, arg_def);
#else
                cnfizeImplies(new_args, arg_def, partitions);
#endif
            else if (logic.isDistinct(tr))
#ifndef PRODUCE_PROOF
                cnfizeDistinct(new_args, arg_def);
#else
                cnfizeDistinct(new_args, arg_def, partitions);
#endif
            else if (logic.isIte(tr))
#ifndef PRODUCE_PROOF
                cnfizeIfthenelse(new_args, arg_def);
#else
                cnfizeIfthenelse(new_args, arg_def);
#endif
            else if (!logic.isNot(tr) && logic.getPterm(tr).size() > 0) {
                // XXX Cnfize equalities here
                if (logic.isEquality(tr)) {
                    ;
                    // This is a bridge equality
                    // It should be treated as a literal by the SAT solver
                }
                if (logic.lookupUPEq(tr) != PTRef_Undef) {
                    // Uninterpreted predicate.  Special handling
                    ;
                }
            }
            else
                cerr << "Operator not handled: " << logic.getSymName(tr) << endl;
            if (arg_def != PTRef_Undef)
                result = arg_def;
        }
        assert(!valdupmap.contains(tr));
        valdupmap.insert(tr, result);
    }

    if (logic.isNot(f)) {
        PTRef tr_clear;
        bool sgn;
        tmap.getTerm(f, tr_clear, sgn);
        vec<Lit> clause;
        if (sgn)
            clause.push(findLit(logic.mkNot(valdupmap[tr_clear])));
        else
            clause.push(findLit(valdupmap[tr_clear]));
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            return addClause(clause, partitions);
#else
        return addClause(clause);
#endif
    }
    return true;
}

#else
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
#endif

#ifdef ENABLE_SHARING_BUG
void Tseitin::cnfizeAnd( vec<PTRef>& args, PTRef arg_def)
{
    if (arg_def == PTRef_Undef) {
        for (int i = 0; i < args.size(); i++) {
            vec<Lit> little_clause;
            little_clause.push(findLit(args[i]));
#ifdef PRODUCE_PROOF
            if (config.produce_inter > 0)
                addClause(little_clause, partitions)
            else
                addClause(little_clause)
#else
            solver.addClause(little_clause);
#endif
        }
    }
    else {
        Lit v = findLit(arg_def);
        vec<Lit> little_clause;
        vec<Lit> big_clause;
        little_clause.push(~v);
        big_clause   .push(v);
        for (int i = 0; i < args.size(); i++) {
            PTRef arg = args[i];
            little_clause.push( findLit(arg) );
            big_clause   .push(~findLit(arg));
#ifdef PRODUCE_PROOF
            if ( config.produce_inter > 0 )
                addClause( little_clause, partitions );
            else
                addClause(little_clause);        // Adds a little clause to the solver
#else
            addClause(little_clause);
#endif
            little_clause.pop();
        }
#ifdef PRODUCE_PROOF
        if ( config.produce_inter > 0 )
            addClause( big_clause, partitions );
        else
            addClause( big_clause );                    // Adds a big clause to the solver
#else
        addClause( big_clause );                    // Adds a big clause to the solver
#endif
    }
}
#else // ENABLE_SHARING_BUG
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

#endif //ENABLE_SHARING_BUG


#ifdef ENABLE_SHARING_BUG
void Tseitin::cnfizeOr(vec<PTRef>& args, PTRef arg_def)
{
    if (arg_def == PTRef_Undef) {
        vec<Lit> big_clause;
        for (int i = 0; i < args.size(); i++)
            big_clause.push(findLit(args[i]));
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            addClause(big_clause, partitions);
        else
            addClause(big_clause);
#else
        addClause(big_clause);
#endif // PRODUCE_PROOF
    } else {
        //
        // ( a_0 | ... | a_{n-1} )
        //
        // <=>
        //
        // aux = ( aux | -a_0 ) & ... & ( aux | -a_{n-1} ) & ( -aux | a_0 | ... | a_{n-1} )
        //
        vec<Lit>    little_clause;
        vec<Lit>    big_clause;
        Lit v = findLit(arg_def);
        little_clause.push( v);
        big_clause   .push(~v);
        for (int i = 0 ; i < args.size(); i++) {
            Lit arg = findLit(args[i]);
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
            addClause(big_clause);                    // Adds a big clause to the solver
#else // PRODUCE_PROOF
        addClause(big_clause);                    // Adds a big clause to the solver
#endif
    }
}

#else // ENABLE_SHARING_BUG
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
#endif // ENABLE_SHARING_BUG

#ifdef ENABLE_SHARING_BUG
void Tseitin::cnfizeXor(vec<PTRef>& args, PTRef arg_def)
{
    if (arg_def == PTRef_Undef) {
        vec<Lit> clause;
        Lit l1 = findLit(args[0]);
        Lit l2 = findLit(args[1]);
        clause.push(l1);
        clause.push(l2);
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            addClause(clause, partitions);
        else
            addClause(clause);
#else
        addClause(clause);
#endif
        clause.clear();
        clause.push(~l1);
        clause.push(~l2);
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            addClause(clause, partitions);
        else
            addClause(clause);
#else
        addClause(clause);
#endif
    } else {
        //
        // ( a_0 xor a_1 )
        //
        // <=>
        //
        // aux = ( -aux | a_0  | a_1 ) & ( -aux | -a_0 | -a_1 ) &
        //       (  aux | -a_0 | a_1 ) & (  aux |  a_0 | -a_1 )
        //

        Lit v = findLit(arg_def);

        Lit arg0 = findLit(args[0]);
        Lit arg1 = findLit(args[1]);
        vec<Lit> clause;

        clause.push(~v);

        // First clause
        clause.push(arg0);
        clause.push(arg1);
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            addClause(clause, partitions);
        else
            addClause(clause); // Adds a little clause to the solver
#else
        addClause(clause); // Adds a little clause to the solver
#endif
        clause.pop();
        clause.pop();

        // Second clause
        clause.push(~arg0);
        clause.push(~arg1);
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            addClause(clause, partitions);
        else
            addClause(clause); // Adds a little clause to the solver
#else
        addClause(clause); // Adds a little clause to the solver
#endif
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
            addClause(clause); // Adds a little clause to the solver
#else
        addClause(clause); // Adds a little clause to the solver
#endif
        clause.pop();
        clause.pop();

        // Fourth clause
        clause.push( arg0);
        clause.push(~arg1);
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            addClause(clause, partitions);
        else
            addClause(clause);           // Adds a little clause to the solver
#else
        addClause(clause);           // Adds a little clause to the solver
#endif
    }
}

#else // ENABLE_SHARING_BUG
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
#endif // ENABLE_SHARING_BUG

#ifdef ENABLE_SHARING_BUG
void Tseitin::cnfizeIff(vec<PTRef>& args, PTRef arg_def)
{
    if (arg_def == PTRef_Undef) {
        Lit l1 = findLit(args[0]);
        Lit l2 = findLit(args[1]);
        vec<Lit> clause;
        clause.push(l1);
        clause.push(~l2);
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            addClause(clause, partitions);
        else
            addClause(clause);
#else
        addClause(clause);
#endif
    } else {
        //
        // ( a_0 <-> a_1 )
        //
        // <=>
        //
        // aux = ( -aux |  a_0 | -a_1 ) & ( -aux | -a_0 |  a_1 ) &
        //       (  aux |  a_0 |  a_1 ) & (  aux | -a_0 | -a_1 )
        //
        assert(args.size() == 2);
        Lit v = findLit(arg_def);
        Lit arg0 = findLit(args[0]);
        Lit arg1 = findLit(args[1]);
        vec<Lit> clause;

        clause.push(~v);

        // First clause
        clause.push( arg0);
        clause.push(~arg1);
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            addClause(clause, partitions);
        else
            addClause(clause);           // Adds a little clause to the solver
#else
        addClause(clause);           // Adds a little clause to the solver
#endif

        clause.pop();
        clause.pop();

        // Second clause
        clause.push(~arg0);
        clause.push( arg1);
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            addClause(clause, partitions);
        else
            addClause(clause);           // Adds a little clause to the solver
#else
        addClause(clause);           // Adds a little clause to the solver
#endif

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
            addClause(clause);           // Adds a little clause to the solver
#else
        addClause(clause);           // Adds a little clause to the solver
#endif
        clause.pop();
        clause.pop();

        // Fourth clause
        clause.push(~arg0);
        clause.push(~arg1);
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            addClause(clause, partitions);
        else
            addClause(clause);           // Adds a little clause to the solver
#else
        addClause(clause);           // Adds a little clause to the solver
#endif
    }
}
#else // ENABLE_SHARING_BUG
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
#endif // ENABLE_SHARING_BUG

#ifdef ENABLE_SHARING_BUG
void Tseitin::cnfizeIfthenelse(vec<PTRef>& args, PTRef arg_def)
{
    if (arg_def == PTRef_Undef) {
        Lit i = findLit(args[0]);
        Lit t = findLit(args[1]);
        Lit e = findLit(args[2]);

        vec<Lit> clause;
        clause.push(~i);
        clause.push(t);
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            addClause(clause, partitions);
        else
            addClause(clause);
#else
        addClause(clause);
#endif
        clause.pop();
        clause.pop();
        clause.push(i);
        clause.push(e);
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            addClause(clause, partitions);
        else
            addClause(clause);
#else
        addClause(clause);
#endif

    } else {
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
        assert(args.size() == 3);

        Lit v  = findLit(arg_def);
        Lit a0 = findLit(args[0]);
        Lit a1 = findLit(args[1]);
        Lit a2 = findLit(args[2]);

        vec<Lit> clause;
        // Todo: PRODUCE_PROOF
        clause.push(~v); clause.push(~a0); clause.push(a1);
        addClause( clause ); clause.clear();

        clause.push(~v); clause.push(a0); clause.push(a2);
        addClause( clause ); clause.clear();

        clause.push(v); clause.push(~a0); clause.push(~a1);
        addClause( clause ); clause.clear();

        clause.push(v); clause.push(a0); clause.push(~a2);
        addClause( clause );
    }
}
#else // ENABLE_SHARING_BUG
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
#endif // ENABLE_SHARING_BUG

#ifdef ENABLE_SHARING_BUG
void Tseitin::cnfizeImplies(vec<PTRef>& args, PTRef arg_def)
{
    assert(args.size() == 2);
    if (arg_def == PTRef_Undef) {
        Lit l1 = findLit(args[0]);
        Lit l2 = findLit(args[1]);
        vec<Lit> clause;
        clause.push(~l1);
        clause.push(l2);
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            addClause(clause, partitions);
        else
            addClause(clause);
#else
        addClause(clause);
#endif
    } else {
        // ( a_0 => a_1 )
        //
        // <=>
        //
        // aux = ( -aux | -a_0 |  a_1 ) &
        //       (  aux |  a_0 )        &
        //       (  aux | -a_1 )
        //

        Lit v  = findLit(arg_def);
        Lit a0 = findLit(args[0]);
        Lit a1 = findLit(args[1]);

        vec<Lit> clause;

        clause.push(v);
        // TODO: PRODUCE_PROOF
        clause.push(a0);
        addClause(clause); clause.pop();

        clause.push(~a1);
        addClause(clause); clause.clear();

        clause.push(~v); clause.push(~a0); clause.push(a1);
        addClause(clause);
    }
}

#else // ENABLE_SHARING_BUG
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
#endif // ENABLE_SHARING_BUG

// TODO: This does not seem to be the right implementation...
#ifdef ENABLE_SHARING_BUG
void Tseitin::cnfizeDistinct(vec<PTRef>& args, PTRef arg_def)
{
    cnfizeOr(args, arg_def);
}
#else // ENABLE_SHARING_BUG
void Tseitin::cnfizeDistinct( PTRef distinct_term
#ifdef PRODUCE_PROOF
                              , const ipartitions_t partitions
#endif
                              )
{
    cnfizeOr(distinct_term);
}
#endif // ENABLE_SHARING_BUG

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
