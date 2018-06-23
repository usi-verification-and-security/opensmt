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
#include "Global.h"
#include "LA.h"



const char* LRALogic::e_nonlinear_term = "Logic does not support nonlinear terms";

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
/***********************************************************
 * Class defining simplifications
 ***********************************************************/

//
// Identify all constants, and combine them into one using the operator
// rules.  If the constant is special for that operator, do the
// corresponding simplifications.  Examples include 0 with
// multiplication and summation, e.g.
//
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
}

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
      Logic(c)
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

bool LRALogic::isBuiltinFunction(const SymRef sr) const
{
    if (sr == sym_Real_NEG || sr == sym_Real_MINUS || sr == sym_Real_PLUS || sr == sym_Real_TIMES || sr == sym_Real_DIV || sr == sym_Real_EQ || sr == sym_Real_LEQ || sr == sym_Real_LT || sr == sym_Real_GEQ || sr == sym_Real_GT || sr == sym_Real_ITE) return true;
    else return Logic::isBuiltinFunction(sr);
}

const opensmt::Real&
LRALogic::getRealConst(PTRef tr) const
{
    SymId id = sym_store[getPterm(tr).symb()].getId();
    assert(id < reals.size() && reals[id] != NULL);
    return *reals[id];
}

PTRef LRALogic::mkConst(const char *name, const char **msg)
{
    return mkConst(getSort_real(), name);
}

PTRef LRALogic::mkConst(SRef s, const char* name)
{
    assert(strlen(name) != 0);
    PTRef ptr = PTRef_Undef;
    if (s == sort_REAL) {
        char* rat;
        opensmt::stringToRational(rat, name);
        ptr = mkVar(s, rat);
        // Store the value of the number as a real
        SymId id = sym_store[getPterm(ptr).symb()].getId();
        for (int i = reals.size(); i <= id; i++)
            reals.push(NULL);
        if (reals[id] != NULL) { delete reals[id]; }
        reals[id] = new opensmt::Real(rat);
        free(rat);
        // Code to allow efficient constant detection.
        while (id >= constants.size())
            constants.push(false);
        constants[id] = true;
    } else
        ptr = Logic::mkConst(s, name);

    return ptr;
}

bool LRALogic::isRealTerm(PTRef tr) const
{
    const Pterm& t = getPterm(tr);
    if (t.size() == 2 && isRealTimes(tr))
        return ((isRealVar(t[0]) || isUF(t[0])) && isConstant(t[1])) || ((isRealVar(t[1]) || isUF(t[1])) && isConstant(t[0]));
    else if (t.size() == 0)
        return isRealVar(tr) || isConstant(tr);
    else
        return false;
}

bool
LRALogic::okForBoolVar(PTRef tr) const
{
    return isRealLeq(tr) || Logic::okForBoolVar(tr);
}

PTRef LRALogic::insertTerm(SymRef sym, vec<PTRef>& terms, char **msg)
{
    if (sym == sym_Real_NEG)
        return mkRealNeg(terms[0], msg);
    if (sym == sym_Real_MINUS)
        return mkRealMinus(terms, msg);
    if (sym == sym_Real_PLUS)
        return mkRealPlus(terms, msg);
    if (sym == sym_Real_TIMES)
        return mkRealTimes(terms, msg);
    if (sym == sym_Real_DIV)
        return mkRealDiv(terms, msg);
    if (sym == sym_Real_LEQ)
        return mkRealLeq(terms, msg);
    if (sym == sym_Real_LT)
        return mkRealLt(terms, msg);
    if (sym == sym_Real_GEQ)
        return mkRealGeq(terms, msg);
    if (sym == sym_Real_GT)
        return mkRealGt(terms, msg);
    if (sym == sym_Real_ITE)
        return mkIte(terms);

    return Logic::insertTerm(sym, terms, msg);
}

PTRef LRALogic::mkRealNeg(PTRef tr, char** msg)
{
    if (isRealNeg(tr)) return getPterm(tr)[0];
    vec<PTRef> args;
    if (isRealPlus(tr)) {
        for (int i = 0; i < getPterm(tr).size(); i++) {
            PTRef tr_arg = mkRealNeg(getPterm(tr)[i], msg);
            assert(tr_arg != PTRef_Undef);
            args.push(tr_arg);
        }
        PTRef tr_n = mkRealPlus(args, msg);
        assert(tr_n != PTRef_Undef);
        return tr_n;
    }
    if (isConstant(tr)) {
        char* rat_str;
        opensmt::stringToRational(rat_str, sym_store.getName(getPterm(tr).symb()));
        opensmt::Real v(rat_str);
        free(rat_str);
        v = -v;
        PTRef nterm = mkConst(getSort_real(), v.get_str().c_str());
        SymRef s = getPterm(nterm).symb();
        return mkFun(s, args, msg);
    }
    PTRef mo = mkConst(getSort_real(), "-1");
    args.push(mo); args.push(tr);
    return mkRealTimes(args);
}

PTRef LRALogic::mkRealMinus(const vec<PTRef>& args_in, char** msg)
{
    SymRef s;
    vec<PTRef> args;
    args_in.copyTo(args);

    if (args.size() == 1) {
        return mkRealNeg(args[0], msg);
//        s = sym_Real_NEG;
//        return mkFun(s, args, msg);
    }
    assert (args.size() == 2);
    PTRef mo = mkConst(getSort_real(), "-1");
    if (mo == PTRef_Undef) {
        printf("Error: %s\n", *msg);
        assert(false);
    }
    vec<PTRef> tmp;
    tmp.push(mo);
    tmp.push(args[1]);
    PTRef fact = mkRealTimes(tmp, msg);
    if (fact == PTRef_Undef) {
        printf("Error: %s\n", *msg);
        assert(false);
    }
    args[1] = fact;
    return mkRealPlus(args);
}

PTRef LRALogic::mkRealPlus(const vec<PTRef>& args, char** msg)
{
    vec<PTRef> new_args;

    // Flatten possible internal sums.  This needs not be done properly,
    // with a post-order dfs, since we are guaranteed that the inner
    // sums are already flattened.
    for (int i = 0; i < args.size(); i++) {
        if (isRealPlus(args[i])) {
            Pterm& t = getPterm(args[i]);
            for (int j = 0; j < t.size(); j++)
                new_args.push(t[j]);
        } else {
            new_args.push(args[i]);
        }
    }
    vec<PTRef> tmp_args;
    new_args.copyTo(tmp_args);
    //for (int i = 0; i < new_args.size(); i++)
    //    args.push(new_args[i]);

    SimplifyConstSum simp(*this);
    vec<PTRef> args_new;
    SymRef s_new;
    simp.simplify(sym_Real_PLUS, tmp_args, s_new, args_new, msg);
    if (args_new.size() == 1)
        return args_new[0];


    // This code takes polynomials (+ (* v c1) (* v c2)) and converts them to the form (* v c3) where c3 = c1+c2
    VecMap<PTRef,PTRef,PTRefHash> s2t;
    vec<PTRef> keys;
    for (int i = 0; i < args_new.size(); ++i) {
        PTRef v;
        PTRef c;
        splitTermToVarAndConst(args_new[i], v, c);
        if (c == PTRef_Undef) {
            // The term is unit
            c = getTerm_RealOne();
        }
        if (!s2t.has(v)) {
            vec<PTRef> tmp;
            tmp.push(c);
            s2t.insert(v, tmp);
            keys.push(v);
        } else
            s2t[v].push(c);
    }
    vec<PTRef> sum_args;
    for (int i = 0; i < keys.size(); i++) {
        vec<PTRef>& consts = s2t[keys[i]];
        PTRef consts_summed = mkRealPlus(consts);
        vec<PTRef> term_args;
        term_args.push(consts_summed);
        if (keys[i] != PTRef_Undef)
            term_args.push(keys[i]);
        else term_args.push(getTerm_RealOne());
        PTRef term = mkRealTimes(term_args);
        if (!isRealZero(term))
            sum_args.push(term);
    }

    if (sum_args.size() == 1) return sum_args[0];
    PTRef tr = mkFun(s_new, sum_args, msg);
//    PTRef tr = mkFun(s_new, args_new, msg);
    return tr;
}

PTRef LRALogic::mkRealTimes(const vec<PTRef>& tmp_args, char** msg)
{
    vec<PTRef> args;
    // Flatten possible internal multiplications
    for (int i = 0; i < tmp_args.size(); i++) {
        if (isRealTimes(tmp_args[i])) {
            Pterm& t = getPterm(tmp_args[i]);
            for (int j = 0; j < t.size(); j++)
                args.push(t[j]);
        } else {
            args.push(tmp_args[i]);
        }
    }
    SimplifyConstTimes simp(*this);
    vec<PTRef> args_new;
    SymRef s_new;
    simp.simplify(sym_Real_TIMES, args, s_new, args_new, msg);
    PTRef tr = mkFun(s_new, args_new, msg);
    // Either a real term or, if we constructed a multiplication of a
    // constant and a sum, a real sum.
    if (isRealTerm(tr) || isRealPlus(tr) || isUF(tr))
        return tr;
    else {
        char* err;
        asprintf(&err, "%s", printTerm(tr));
        throw LRANonLinearException(err);
    }
}

PTRef LRALogic::mkRealDiv(const vec<PTRef>& args, char** msg)
{
    SimplifyConstDiv simp(*this);
    vec<PTRef> args_new;
    SymRef s_new;

    simp.simplify(sym_Real_DIV, args, s_new, args_new, msg);
    assert(args.size() == 2);

    if (isRealDiv(s_new)) {
        assert(isRealTerm(args_new[0]) && isConstant(args_new[1]));
        args_new[1] = mkConst(FastRational_inverse(getRealConst(args_new[1]))); //mkConst(1/getRealConst(args_new[1]));
        return mkRealTimes(args_new);
    }

    PTRef tr = mkFun(s_new, args_new, msg);
    return tr;
}

// Find the lexicographically first factor of a term and divide the other terms with it.
PTRef LRALogic::normalizeSum(PTRef sum) {
    vec<PTRef> args;
    Pterm& s = getPterm(sum);
    for  (int i = 0; i < s.size(); i++)
        args.push(s[i]);
    termSort(args);
    PTRef const_term = PTRef_Undef;
    for (int i = 0; i < args.size(); i++) {
        if (isRealVar(args[i])) {
            // The lex first term has an implicit unit factor, no need to do anything.
            return sum;
        }
        if (isRealTimes(args[i])) {
            assert(!isRealZero(getPterm(args[i])[0]) && !isRealZero(getPterm(args[i])[1]));
            const_term = args[i];
            break;
        }
    }

    if (const_term == PTRef_Undef) {
        // No factor qualifies, only constants in the sum
        return sum;
    }

    // here we have const_term != PTRef_Undef
    Pterm& t = getPterm(const_term);
    assert(t.size() == 2);
    assert(isConstant(t[0]) || isConstant(t[1]));
    // We need to go through the real values since negative constant
    // terms are are not real negations.
    opensmt::Real k = abs(isConstant(t[0]) ? getRealConst(t[0]) : getRealConst(t[1]));
    PTRef divisor = mkConst(k);
    for (int i = 0; i < args.size(); i++) {
        vec<PTRef> tmp;
        tmp.push(args[i]);
        tmp.push(divisor);
        args[i] = mkRealDiv(tmp);
    }
    return mkRealPlus(args);
}

//
// Input is expected to be of the following forms:
// (0a)  a
// (0b)  -a
// (1a)  x
// (2a) (* a x)
// (2b) (* x a)
// (2c) (* -a x)
// (2d) (* a -x)
// (3a) (+ (* a x) t_1 ... t_n)
// (3b) (+ (* -a x) t_1 ... t_n)
// (3c) (+ (* x a) t_1 ... t_n)
// (3d) (+ (* x -a) t_1 ... t_n)
// (3e) (+ x t_1 ... t_n)
// Returns true for cases (1d), (1e), (2b), and (2d), and false for other cases.
//
bool LRALogic::isNegated(PTRef tr) const {
    if (isRealConst(tr))
        return getRealConst(tr) < 0; // Case (0a) and (0b)
    if (isRealVar(tr))
        return false; // Case (1a)
    if (isRealTimes(tr)) {
        // Cases (2)
        PTRef v;
        PTRef c;
        splitTermToVarAndConst(tr, v, c);
        return isNegated(c);
    }
    else {
        // Cases(3)
        return isNegated(getPterm(tr)[0]);
    }
}

void LRALogic::splitTermToVarAndConst(const PTRef& term, PTRef& var, PTRef& fac) const
{
    assert(isRealTimes(term) || isRealDiv(term) || isRealVar(term) || isConstant(term) || isUF(term));
    if (isRealTimes(term) || isRealDiv(term)) {
        assert(getPterm(term).size() == 2);
        fac = getPterm(term)[0];
        var = getPterm(term)[1];
        if (!isConstant(fac)) {
            PTRef t = var;
            var = fac;
            fac = t;
        }
        assert(isConstant(fac));
        assert(isRealVar(var) || isUF(var));
    } else if (isRealVar(term) || isUF(term)) {
        var = term;
        fac = getTerm_RealOne();
    } else {
        var = getTerm_RealOne();
        fac = term;
    }
}


// Normalize a product of the form (* a v) to either v or (* -1 v)
PTRef LRALogic::normalizeMul(PTRef mul)
{
    assert(isRealTimes(mul));
    PTRef v = PTRef_Undef;
    PTRef c = PTRef_Undef;
    splitTermToVarAndConst(mul, v, c);
    opensmt::Real r = getRealConst(c);
    if (r < 0)
        return mkRealNeg(v);
    else
        return v;
}

// If the call results in a leq it is guaranteed that arg[0] is a
// constant, and arg[1][0] has factor 1 or -1
PTRef LRALogic::mkRealLeq(const vec<PTRef>& args_in, char** msg)
{
    vec<PTRef> args;
    args_in.copyTo(args);
    assert(args.size() == 2);

    if (isConstant(args[0]) && isConstant(args[1])) {
        opensmt::Real v1(sym_store.getName(getPterm(args[0]).symb()));
        opensmt::Real v2(sym_store.getName(getPterm(args[1]).symb()));
        if (v1 <= v2)
            return getTerm_true();
        else
            return getTerm_false();

    } else {

        // Should be in the form that on one side there is a constant
        // and on the other there is a sum
        PTRef tr_neg = mkRealNeg(args[0], msg);
        vec<PTRef> sum_args;
        sum_args.push(args[1]);
        sum_args.push(tr_neg);
        PTRef sum_tmp = mkRealPlus(sum_args, msg); // This gives us a collapsed version of the sum
        if (isConstant(sum_tmp)) {
            args[0] = getTerm_RealZero();
            args[1] = sum_tmp;
            return mkRealLeq(args, msg); // either true or false
        } if (isRealTimes(sum_tmp)) {
            sum_tmp = normalizeMul(sum_tmp);
        } else if (isRealPlus(sum_tmp)) {
            // Normalize the sum
            sum_tmp = normalizeSum(sum_tmp); //Now the sum is normalized by dividing with the "first" factor.
        }
        // Otherwise no operation, already normalized

        vec<PTRef> nonconst_args;
        PTRef c = PTRef_Undef;
        if (isRealPlus(sum_tmp)) {
            Pterm& t = getPterm(sum_tmp);
            for (int i = 0; i < t.size(); i++) {
                if (!isConstant(t[i]))
                    nonconst_args.push(t[i]);
                else {
                    assert(c == PTRef_Undef);
                    c = t[i];
                }
            }
            if (c == PTRef_Undef) {
                args[0] = getTerm_RealZero();
                args[1] = mkRealPlus(nonconst_args);
            } else {
                args[0] = mkRealNeg(c);
                args[1] = mkRealPlus(nonconst_args);
            }
        } else if (isRealVar(sum_tmp) || isRealTimes(sum_tmp)) {
            args[0] = getTerm_RealZero();
            args[1] = sum_tmp;
        } else assert(false);

        PTRef r = mkFun(sym_Real_LEQ, args, msg);
        return r;
    }
}

PTRef LRALogic::mkRealGeq(const vec<PTRef>& args, char** msg)
{
    vec<PTRef> new_args;
    new_args.push(args[1]);
    new_args.push(args[0]);
    return mkRealLeq(new_args, msg);
}

PTRef LRALogic::mkRealLt(const vec<PTRef>& args, char** msg)
{
    if (isConstant(args[0]) && isConstant(args[1])) {
        char *rat_str1, *rat_str2;
        opensmt::stringToRational(rat_str1, sym_store.getName(getPterm(args[0]).symb()));
        opensmt::stringToRational(rat_str2, sym_store.getName(getPterm(args[1]).symb()));
        opensmt::Real v1(rat_str1);
        opensmt::Real v2(rat_str2);
        free(rat_str1);
        free(rat_str2);
        if (v1 < v2) {
            return getTerm_true();
        } else {
            return getTerm_false();
        }
    }
    vec<PTRef> tmp;
    tmp.push(args[1]);
    tmp.push(args[0]);
    PTRef tr = mkRealLeq(tmp, msg);
    if (tr == PTRef_Undef) {
        printf("%s\n", *msg);
        assert(false);
    }
    return mkNot(tr);
}

PTRef LRALogic::mkRealGt(const vec<PTRef>& args, char** msg)
{
    if (isConstant(args[0]) && isConstant(args[1])) {
        char *rat_str1, *rat_str2;
        opensmt::stringToRational(rat_str1, sym_store.getName(getPterm(args[0]).symb()));
        opensmt::stringToRational(rat_str2, sym_store.getName(getPterm(args[1]).symb()));
        opensmt::Real v1(rat_str1);
        opensmt::Real v2(rat_str2);
        free(rat_str1);
        free(rat_str2);
        if (v1 > v2)
            return getTerm_true();
        else
            return getTerm_false();
    }
    PTRef tr = mkRealLeq(args, msg);
    if (tr == PTRef_Undef) {
        printf("%s\n", *msg);
        assert(false);
    }
    return mkNot(tr);
}



// Return a term corresponding to the operation applied to the constant
// terms.  The list may contain terms of the form (* -1 a) for constant
// a.

PTRef SimplifyConst::simplifyConstOp(const vec<PTRef>& terms, char** msg)
{
    opensmt::Real s = getIdOp();
    if (terms.size() == 0) {
        opensmt::Real s = getIdOp();
        return l.mkConst(l.getSort_real(), s.get_str().c_str());
    } else if (terms.size() == 1) {
        char* rat_str;
        opensmt::stringToRational(rat_str, l.getSymName(terms[0]));
        opensmt::Real val(rat_str);
        free(rat_str);
        return l.mkConst(l.getSort_real(), val.get_str().c_str());
    } else {
        char* rat_str;
        opensmt::stringToRational(rat_str, l.getSymName(terms[0]));
        opensmt::Real s(rat_str);
        free(rat_str);
        for (int i = 1; i < terms.size(); i++) {
            PTRef tr = PTRef_Undef;
            if (l.isConstant(terms[i]))
                tr = terms[i];
            else if (l.isRealNeg(terms[i]))
                tr = l.getPterm(terms[i])[0];
            else continue;
            char* rat_str;
            opensmt::stringToRational(rat_str, l.getSymName(tr));

            opensmt::Real val(rat_str);
            free(rat_str);
            Op(s, val);
        }
        return l.mkConst(l.getSort_real(), s.get_str().c_str());
    }
}

lbool LRALogic::retrieveSubstitutions(vec<PtAsgn>& facts, Map<PTRef,PtAsgn,PTRefHash>& substs)
{
    lbool res = Logic::retrieveSubstitutions(facts, substs);
    if (res != l_Undef) return res;
    vec<PTRef> top_level_arith;
    for (int i = 0; i < facts.size(); i++) {
        PTRef tr = facts[i].tr;
        lbool sgn = facts[i].sgn;
        if (isRealEq(tr) && sgn == l_True)
            top_level_arith.push(tr);
    }

    return arithmeticElimination(top_level_arith, substs);
}

lbool LRALogic::arithmeticElimination(vec<PTRef> &top_level_arith, Map<PTRef,PtAsgn,PTRefHash>& substitutions)
{
    vec<LAExpression*> equalities;
    LRALogic& logic = *this;
    // I don't know if reversing the order makes any sense but osmt1
    // does that.
    for (int i = top_level_arith.size()-1; i >= 0; i--) {
        equalities.push(new LAExpression(logic, top_level_arith[i]));
    }
#ifdef SIMPLIFY_DEBUG
    for (int i = 0; i < equalities.size(); i++) {
        cerr << "; ";
        equalities[i]->print(cerr);
        cerr << endl;
    }
#endif
    //
    // If just one equality, produce substitution right away
    //
    if ( equalities.size( ) == 0 )
        ; // Do nothing
    else if ( equalities.size( ) == 1 ) {
        LAExpression & lae = *equalities[ 0 ];
        if (lae.solve() == PTRef_Undef) {
            // Constant substituted by a constant.  No new info from
            // here.
//            printf("there is something wrong here\n");
            return l_Undef;
        }
        pair<PTRef, PTRef> sub = lae.getSubst();
        assert( sub.first != PTRef_Undef );
        assert( sub.second != PTRef_Undef );
        if(substitutions.has(sub.first))
        {
            //cout << "ARITHMETIC ELIMINATION FOUND DOUBLE SUBSTITUTION:\n" << printTerm(sub.first) << " <- " << printTerm(sub.second) << " | " << printTerm(substitutions[sub.first].tr) << endl;
            if(sub.second != substitutions[sub.first].tr)
                return l_False;
        } else
            substitutions.insert(sub.first, PtAsgn(sub.second, l_True));
    } else {
        // Otherwise obtain substitutions
        // by means of Gaussian Elimination
        //
        // FORWARD substitution
        // We put the matrix equalities into upper triangular form
        //
        for (uint32_t i = 0; i < equalities.size()-1; i++) {
            LAExpression &s = *equalities[i];
            // Solve w.r.t. first variable
            if (s.solve( ) == PTRef_Undef) {
                if (logic.isTrue(s.toPTRef())) continue;
                assert(logic.isFalse(s.toPTRef()));
                return l_False;
            }
            // Use the first variable x in s to generate a
            // substitution and replace x in lac
            for ( unsigned j = i + 1 ; j < equalities.size( ) ; j ++ ) {
                LAExpression & lac = *equalities[ j ];
                combine( s, lac );
            }
        }
        //
        // BACKWARD substitution
        // From the last equality to the first we put
        // the matrix equalities into canonical form
        //
        for (int i = equalities.size() - 1; i >= 1; i--) {
            LAExpression & s = *equalities[i];
            // Solve w.r.t. first variable
            if (s.solve() == PTRef_Undef) {
                if (logic.isTrue(s.toPTRef())) continue;
                assert(logic.isFalse(s.toPTRef()));
                return l_False;
            }
            // Use the first variable x in s as a
            // substitution and replace x in lac
            for (int j = i - 1; j >= 0; j--) {
                LAExpression& lac = *equalities[j];
                combine(s, lac);
            }
        }
        //
        // Now, for each row we get a substitution
        //
        for (unsigned i = 0 ;i < equalities.size(); i++) {
            LAExpression& lae = *equalities[i];
            pair<PTRef, PTRef> sub = lae.getSubst();
            if (sub.first == PTRef_Undef) continue;
            assert(sub.second != PTRef_Undef);
            //cout << printTerm(sub.first) << " <- " << printTerm(sub.second) << endl;
            if(!substitutions.has(sub.first)) {
                substitutions.insert(sub.first, PtAsgn(sub.second, l_True));
//                cerr << "; gaussian substitution: " << logic.printTerm(sub.first) << " -> " << logic.printTerm(sub.second) << endl;
            } else {
                if (isConstant(sub.second) && isConstant(sub.first) && (sub.second != substitutions[sub.first].tr))
                    return l_False;
            }
        }
    }
    // Clean constraints
    for (int i = 0; i < equalities.size(); i++)
        delete equalities[i];

    return l_Undef;
}

//
// LRALogic data contains Logic data and the maps for reals.
// +-------------------------------------------------+
// |size| ... <data defined by logic> ...            |
// |reals_size| <reals_data>                         |
// +-------------------------------------------------+
//
void LRALogic::serializeLogicData(int*& logicdata_buf) const
{
    Logic::serializeLogicData(logicdata_buf);
    vec<SymRef> real_syms;
    for (int i = 0; i < reals.size(); i++)
        if (reals[i] != NULL)
            real_syms.push(sym_store.symbols[i]);

#ifdef VERBOSE_FOPS
    printf("Found %d real symbols\n", real_syms.size());
#endif
    int size_old = logicdata_buf[buf_sz_idx];
    int size_new = size_old + real_syms.size() + 2;
    logicdata_buf = (int*) realloc(logicdata_buf, size_new*sizeof(int));
    logicdata_buf[size_old] = real_syms.size();
    for (int i = 0; i < real_syms.size(); i++)
        logicdata_buf[size_old+1+i] = real_syms[i].x;
    logicdata_buf[buf_sz_idx] = size_new;
}

void LRALogic::deserializeLogicData(const int* logicdata_buf)
{
    Logic::deserializeLogicData(logicdata_buf);
    int mydata_init = logicdata_buf[constants_offs_idx] + logicdata_buf[logicdata_buf[constants_offs_idx]];
    assert(mydata_init < logicdata_buf[0]); // Inside the buffer still
    int sz = logicdata_buf[mydata_init];
    for (int i = 0; i < sz; i++) {
        SymRef sr = {(uint32_t) logicdata_buf[mydata_init+1+i]};
        SymId id = sym_store[sr].getId();
        for (int j = reals.size(); j <= id; j++)
            reals.push(NULL);
        reals[id] = new opensmt::Real(sym_store.idToName[id]);
        while (id >= constants.size())
            constants.push(false);
        constants[id] = true;
    }
}

// Handle the printing of real constants that are negative and the
// rational constants
char*
LRALogic::printTerm_(PTRef tr, bool ext, bool safe) const
{
    char* out;
    if (isRealConst(tr))
    {
        bool is_neg = false;
        char* tmp_str;
        opensmt::stringToRational(tmp_str, sym_store.getName(getPterm(tr).symb()));
        opensmt::Real v(tmp_str);
        if (!isNonnegRealConst(tr))
        {
            v = -v;
            is_neg = true;
        }
        char* rat_str = strdup(v.get_str().c_str());
        free(tmp_str);

        bool is_div = false;
        int i = 0;
        for (; rat_str[i] != '\0'; i++)
        {
            if (rat_str[i] == '/')
            {
                is_div = true;
                break;
            }
        }
        if (is_div)
        {
            int j = 0;
            char* nom = (char*) malloc(i+1);
            for (; j < i; j++)
                nom[j] = rat_str[j];
            nom[i] = '\0';
            int len = strlen(rat_str);
            char* den = (char*) malloc(len-i);
            i++;
            j = 0;
            for (; i < len; i++)
                den[j++] = rat_str[i];
            den[j] = '\0';

            if (ext) {
                if (is_neg)
                    asprintf(&out, "(/ (- %s) %s) <%d>", nom, den, tr.x);
                else
                    asprintf(&out, "(/ %s %s) <%d>", nom, den, tr.x);
            }
            else {
                if (is_neg)
                    asprintf(&out, "(/ (- %s) %s)", nom, den);
                else
                    asprintf(&out, "(/ %s %s)", nom, den);
            }
            free(nom);
            free(den);
        }
        else if (is_neg) {
            if (ext)
                asprintf(&out, "(- %s) <%d>", rat_str, tr.x);
            else
                asprintf(&out, "(- %s)", rat_str);
        }
        else
            out = rat_str;
    }
    else
        out = Logic::printTerm_(tr, ext, safe);
    return out;
}

