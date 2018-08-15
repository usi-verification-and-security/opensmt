/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

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
#include "SStore.h"
#include "PtStore.h"
#include "LRALogic.h"
#include "TreeOps.h"
//#include "Global.h"
//#include "LA.h"
const char* LRALogic::e_nonlinear_term = "Logic does not support nonlinear terms";
/*
void LRALogic::termSort(vec<PTRef>& v) const
{
    sort(v, LessThan_deepPTRef(this));
}


void LRALogic::simplifyAndSplitEq(PTRef tr, PTRef& root_out)
{
    split_eq = true;
    simplifyTree(tr, root_out);
    split_eq = false;
}



void LRALogic::visit(PTRef tr, Map<PTRef,PTRef,PTRefHash>& tr_map)
{
    if (split_eq && isRealEq(tr)) {
        char *msg;
        Pterm& p = getPterm(tr);
        PTRef a1 = p[0];
        PTRef a2 = p[1];
        vec<PTRef> args;
        args.push(a1); args.push(a2);
        PTRef i1 = mkRealLeq(args, &msg);
        PTRef i2 = mkRealGeq(args, &msg);
#ifdef PRODUCE_PROOF
        ipartitions_t &part = getIPartitions(tr);
        addIPartitions(i1, part);
        addIPartitions(i2, part);
#endif
        args.clear();
        args.push(i1); args.push(i2);
        PTRef andr = mkAnd(args);
        lra_split_inequalities.insert(i1, true);
        lra_split_inequalities.insert(i2, true);
#ifdef PRODUCE_PROOF
        if (hasOriginalAssertion(tr)) {
            PTRef orig = getOriginalAssertion(tr);
            setOriginalAssertion(andr, orig);
        }
#endif
        assert(!tr_map.has(tr));
        tr_map.insert(tr, andr);
    }
    Logic::visit(tr, tr_map);
}

bool LRALogic::okToPartition(PTRef tr) const
{
    return !lra_split_inequalities.has(tr);
}


*/
/***********************************************************
 * Class defining simplifications
 ***********************************************************/
//
// Identify all constants, and combine them into one using the operator
// rules.  If the constant is special for that operator, do the
// corresponding simplifications.  Examples include 0 with
// multiplication and summation, e.g.
//
/*
void SimplifyConst::simplify(SymRef& s, const vec<PTRef>& args, SymRef& s_new, vec<PTRef>& args_new, char** msg)
{
    vec<int> const_idx;
    vec<PTRef> args_new_2;
    for (int i = 0; i < args.size(); i++) {
        if (l.isConstant(args[i]) || (l.isRealNeg(args[i]) && l.isConstant(l.getPterm(args[i])[0])))
            const_idx.push(i);
    }
    if (const_idx.size() > 1) {
        vec<PTRef> const_terms;
        for (int i = 0; i < const_idx.size(); i++)
            const_terms.push(args[const_idx[i]]);

        PTRef tr = simplifyConstOp(const_terms, msg);
        if (tr == PTRef_Undef) {
            printf("%s\n", *msg);
            assert(false);
        }
        int i, j, k;
        for (i = j = k = 0; i < args.size() && k < const_terms.size(); i++) {
            if (i != const_idx[k]) args_new_2.push(args[i]);
            else k++;
        }
        // Copy also the rest
        for (; i < args.size(); i++)
            args_new_2.push(args[i]);
        args_new_2.push(tr);
    } else
        args.copyTo(args_new_2);

    constSimplify(s, args_new_2, s_new, args_new);
    // A single argument for the operator, and the operator is identity
    // in that case
    if (args_new.size() == 1 && (l.isRealPlus(s_new) || l.isRealTimes(s_new) || l.isRealDiv(s_new))) {
        PTRef ch_tr = args_new[0];
        args_new.clear();
        s_new = l.getPterm(ch_tr).symb();
        for (int i = 0; i < l.getPterm(ch_tr).size(); i++)
            args_new.push(l.getPterm(ch_tr)[i]);
    }
}

void SimplifyConstSum::constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const
{
    assert(terms_new.size() == 0);
    int i;
    for (i = 0; i < terms.size(); i++)
        if (!l.isRealZero(terms[i]))
            terms_new.push(terms[i]);
    if (terms_new.size() == 0) {
        // The term was sum of all zeroes
        terms_new.clear();
        s_new = l.getPterm(l.getTerm_RealZero()).symb();
        return;
    }
    s_new = s;
}

void SimplifyConstTimes::constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const
{
    //distribute the constant over the first sum
    int i;
    PTRef con, plus;
    con = plus = PTRef_Undef;
    for (i = 0; i < terms.size(); i++) {
        if (l.isRealZero(terms[i])) {
            terms_new.clear();
            s_new = l.getPterm(l.getTerm_RealZero()).symb();
            return;
        }
        if (!l.isRealOne(terms[i]))
        {
            if(l.isRealPlus(terms[i]))
                plus = terms[i];
            else if(l.isConstant(terms[i]))
                con = terms[i];
            else
                terms_new.push(terms[i]);
        }
    }
    if(con == PTRef_Undef && plus == PTRef_Undef);
    else if(con == PTRef_Undef && plus != PTRef_Undef)
        terms_new.push(plus);
    else if(con != PTRef_Undef && plus == PTRef_Undef)
        terms_new.push(con);
    else
    {
        Pterm& p = l.getPterm(plus);
        vec<PTRef> sum_args;
        for(int i = 0; i < p.size(); ++i)
        {
            vec<PTRef> times_args;
            times_args.push(con);
            times_args.push(p[i]);
            sum_args.push(l.mkRealTimes(times_args));
        }
        terms_new.push(l.mkRealPlus(sum_args));
    }
    if (terms_new.size() == 0) {
        // The term was multiplication of all ones
        terms_new.clear();
        s_new = l.getPterm(l.getTerm_RealOne()).symb();
        return;
    }
    s_new = s;
}

void SimplifyConstDiv::constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const
{
    assert(terms_new.size() == 0);
    assert(terms.size() <= 2);
    if (terms.size() == 2 && l.isRealZero(terms[1])) {
        printf("Explicit div by zero\n");
        assert(false);
    }
    if (l.isRealOne(terms[terms.size()-1])) {
        terms_new.clear();
        s_new = l.getPterm(terms[0]).symb();
        for (int i = 0; i < l.getPterm(terms[0]).size(); i++)
            terms_new.push(l.getPterm(terms[0])[i]);
        return;
    }
    else if (l.isRealZero(terms[0])) {
        terms_new.clear();
        s_new = l.getPterm(terms[0]).symb();
        return;
    }
    for (int i = 0; i < terms.size(); i++)
        terms_new.push(terms[i]);
    s_new = s;
}*/
//const char* LRALogic::tk_val_real_default = "1";
const char* LRALogic::tk_real_zero  = "0";
const char* LRALogic::tk_real_one   = "1";
const char* LRALogic::tk_real_neg   = "-";
const char* LRALogic::tk_real_minus = "-";
const char* LRALogic::tk_real_plus  = "+";
const char* LRALogic::tk_real_times = "*";
const char* LRALogic::tk_real_div   = "/";
const char* LRALogic::tk_real_lt    = "<";
const char* LRALogic::tk_real_leq   = "<=";
const char* LRALogic::tk_real_gt    = ">";
const char* LRALogic::tk_real_geq   = ">=";
const char* LRALogic::s_sort_real = "Real";

LRALogic::LRALogic(SMTConfig& c) :
        LALogic(c)
        , sym_Real_ZERO(SymRef_Undef)
        , sym_Real_ONE(SymRef_Undef)
        , sym_Real_NEG(SymRef_Undef)
        , sym_Real_MINUS(SymRef_Undef)
        , sym_Real_PLUS(SymRef_Undef)
        , sym_Real_TIMES(SymRef_Undef)
        , sym_Real_DIV(SymRef_Undef)
        , sym_Real_EQ(SymRef_Undef)
        , sym_Real_LEQ(SymRef_Undef)
        , sym_Real_LT(SymRef_Undef)
        , sym_Real_GEQ(SymRef_Undef)
        , sym_Real_GT(SymRef_Undef)
        , sym_Real_ITE(SymRef_Undef)
        , sort_REAL(SRef_Undef)
        , term_Real_ZERO(PTRef_Undef)
        , term_Real_ONE(PTRef_Undef)
        , split_eq(false)
{
    char* m;
    char** msg = &m;
    logic_type = QF_LRA;
    sort_REAL = declareSort(s_sort_real, msg);
    ufsorts.remove(sort_REAL);
//    printf("Setting sort_REAL to %d at %p\n", sort_REAL.x, &(sort_REAL.x));
    vec<SRef> params;
    term_Real_ZERO = mkConst(sort_REAL, tk_real_zero);
    sym_Real_ZERO  = getSymRef(term_Real_ZERO);
    sym_store.setInterpreted(sym_Real_ZERO);
    term_Real_ONE  = mkConst(sort_REAL, tk_real_one);
    sym_Real_ONE   = getSymRef(term_Real_ONE);
    sym_store.setInterpreted(sym_Real_ONE);
    params.push(sort_REAL);
    // Negation
    sym_Real_NEG = declareFun(tk_real_neg, sort_REAL, params, msg, true);
    sym_store.setInterpreted(sym_Real_NEG);
    params.push(sort_REAL);
    sym_Real_MINUS = declareFun(tk_real_neg, sort_REAL, params, msg, true);
    sym_store[sym_Real_MINUS].setLeftAssoc();
    sym_store.setInterpreted(sym_Real_MINUS);
    sym_Real_PLUS  = declareFun(tk_real_plus, sort_REAL, params, msg, true);
    sym_store[sym_Real_PLUS].setNoScoping();
    sym_store[sym_Real_PLUS].setCommutes();
    sym_store[sym_Real_PLUS].setLeftAssoc();
    sym_store.setInterpreted(sym_Real_PLUS);
    sym_Real_TIMES = declareFun(tk_real_times, sort_REAL, params, msg, true);
    sym_store[sym_Real_TIMES].setNoScoping();
    sym_store[sym_Real_TIMES].setLeftAssoc();
    sym_store[sym_Real_TIMES].setCommutes();
    sym_store.setInterpreted(sym_Real_TIMES);
    sym_Real_DIV   = declareFun(tk_real_div, sort_REAL, params, msg, true);
    sym_store[sym_Real_DIV].setNoScoping();
    sym_store[sym_Real_DIV].setLeftAssoc();
    sym_store.setInterpreted(sym_Real_DIV);
    sym_Real_LEQ  = declareFun(tk_real_leq, sort_BOOL, params, msg, true);
    sym_store[sym_Real_LEQ].setNoScoping();
    sym_store[sym_Real_LEQ].setChainable();
    sym_store.setInterpreted(sym_Real_LEQ);
    sym_Real_LT   = declareFun(tk_real_lt, sort_BOOL, params, msg, true);
    sym_store[sym_Real_LT].setNoScoping();
    sym_store[sym_Real_LT].setChainable();
    sym_store.setInterpreted(sym_Real_LT);
    sym_Real_GEQ  = declareFun(tk_real_geq, sort_BOOL, params, msg, true);
    sym_store[sym_Real_GEQ].setNoScoping();
    sym_store[sym_Real_GEQ].setChainable();
    sym_store.setInterpreted(sym_Real_GEQ);
    sym_Real_GT   = declareFun(tk_real_gt, sort_BOOL, params, msg, true);
    sym_store[sym_Real_GT].setNoScoping();
    sym_store[sym_Real_GT].setChainable();
    sym_store.setInterpreted(sym_Real_GEQ);
    vec<SRef> ite_params;
    ite_params.push(sort_BOOL);
    ite_params.push(sort_REAL);
    ite_params.push(sort_REAL);
    sym_Real_ITE = declareFun(tk_ite, sort_REAL, ite_params, msg, true);
    //sym_store[sym_Real_ITE].setLeftAssoc();
    sym_store[sym_Real_ITE].setNoScoping();
    sym_store.setInterpreted(sym_Real_ITE);
}

const SymRef LRALogic::get_sym_Num_TIMES () const {return sym_Real_TIMES;}
const SymRef LRALogic::get_sym_Num_DIV () const {return sym_Real_DIV;}
const SymRef LRALogic::get_sym_Num_MINUS () const {return sym_Real_MINUS;}
const SymRef LRALogic::get_sym_Num_PLUS () const {return sym_Real_PLUS;}
const SymRef LRALogic::get_sym_Num_NEG () const {return sym_Real_NEG;}
const SymRef LRALogic::get_sym_Num_LEQ () const {return sym_Real_LEQ;}
const SymRef LRALogic::get_sym_Num_GEQ () const {return sym_Real_GEQ;}
const SymRef LRALogic::get_sym_Num_LT () const {return sym_Real_LT;}
const SymRef LRALogic::get_sym_Num_GT () const {return sym_Real_GT;}
const SymRef LRALogic::get_sym_Num_EQ () const {return sym_Real_EQ;}
const SymRef LRALogic::get_sym_Num_ZERO () const {return sym_Real_ZERO;}
const SymRef LRALogic::get_sym_Num_ONE () const {return sym_Real_ONE;}
const SymRef LRALogic::get_sym_Num_ITE () const {return sym_Real_ITE;}
const SRef LRALogic::get_sort_NUM () const {return sort_REAL;}

PTRef    LRALogic::getTerm_NumZero() const  { return term_Real_ZERO; }
PTRef      LRALogic::getTerm_NumOne()  const  { return term_Real_ONE; }
bool        LRALogic::hasSortNum(PTRef tr) const  { return hasSortReal(getPterm(tr).symb()); }

//bool        LRALogic::hasSortNum(PTRef tr) const  { return hasSortInt(getPterm(tr).symb()); }