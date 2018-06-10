#include "SStore.h"
#include "PtStore.h"
#include "LIALogic.h"
#include "TreeOps.h"
#include "Global.h"
#include "LA.h"

const char* LIALogic::e_nonlinear_term = "Logic does not support nonlinear terms";

void LIALogic::termSort(vec<PTRef>& v) const
{
    sort(v, LessThan_deepPTRef(this));
}

void
LIALogic::simplifyAndSplitEq(PTRef tr, PTRef& root_out)
{
    split_eq = true;
    simplifyTree(tr, root_out);
    split_eq = false;
}

void
LIALogic::visit(PTRef tr, Map<PTRef,PTRef,PTRefHash>& tr_map)
{
    if (split_eq && isIntEq(tr)) {
        char *msg;
        Pterm& p = getPterm(tr);
        PTRef a1 = p[0];
        PTRef a2 = p[1];
        vec<PTRef> args;
        args.push(a1); args.push(a2);
        PTRef i1 = mkIntLeq(args, &msg);
        PTRef i2 = mkIntGeq(args, &msg);
#ifdef PRODUCE_PROOF
        ipartitions_t &part = getIPartitions(tr);
        addIPartitions(i1, part);
        addIPartitions(i2, part);
#endif
        args.clear();
        args.push(i1); args.push(i2);
        PTRef andr = mkAnd(args);
        lia_split_inequalities.insert(i1, true);
        lia_split_inequalities.insert(i2, true);
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

bool LIALogic::okToPartition(PTRef tr) const
{
    return !lia_split_inequalities.has(tr);
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
        if (l.isConstant(args[i]) || (l.isIntNeg(args[i]) && l.isConstant(l.getPterm(args[i])[0])))
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
    if (args_new.size() == 1 && (l.isIntPlus(s_new) || l.isIntTimes(s_new) || l.isIntDiv(s_new))) {
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
        if (!l.isIntZero(terms[i]))
            terms_new.push(terms[i]);
    if (terms_new.size() == 0) {
        // The term was sum of all zeroes
        terms_new.clear();
        s_new = l.getPterm(l.getTerm_IntZero()).symb();
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
        if (l.isIntZero(terms[i])) {
            terms_new.clear();
            s_new = l.getPterm(l.getTerm_IntZero()).symb();
            return;
        }
        if (!l.isIntOne(terms[i]))
        {
            if(l.isIntPlus(terms[i]))
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
            sum_args.push(l.mkIntTimes(times_args));
        }
        terms_new.push(l.mkIntPlus(sum_args));
    }
    if (terms_new.size() == 0) {
        // The term was multiplication of all ones
        terms_new.clear();
        s_new = l.getPterm(l.getTerm_IntOne()).symb();
        return;
    }
    s_new = s;
}

void SimplifyConstDiv::constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const
{
    assert(terms_new.size() == 0);
    assert(terms.size() <= 2);
    if (terms.size() == 2 && l.isIntZero(terms[1])) {
        printf("Explicit div by zero\n");
        assert(false);
    }
    if (l.isIntOne(terms[terms.size()-1])) {
        terms_new.clear();
        s_new = l.getPterm(terms[0]).symb();
        for (int i = 0; i < l.getPterm(terms[0]).size(); i++)
            terms_new.push(l.getPterm(terms[0])[i]);
        return;
    }
    else if (l.isIntZero(terms[0])) {
        terms_new.clear();
        s_new = l.getPterm(terms[0]).symb();
        return;
    }
    for (int i = 0; i < terms.size(); i++)
        terms_new.push(terms[i]);
    s_new = s;
}

const char* LIALogic::tk_int_zero  = "0";
const char* LIALogic::tk_int_one   = "1";
const char* LIALogic::tk_int_neg   = "-";
const char* LIALogic::tk_int_minus = "-";
const char* LIALogic::tk_int_plus  = "+";
const char* LIALogic::tk_int_times = "*";
const char* LIALogic::tk_int_div   = "/";
const char* LIALogic::tk_int_lt    = "<";
const char* LIALogic::tk_int_leq   = "<=";
const char* LIALogic::tk_int_gt    = ">";
const char* LIALogic::tk_int_geq   = ">=";
const char* LIALogic::tk_int_gt    = ">";
const char* LIALogic::tk_int_geq   = ">=";
//mod and abs are needed?

const char* LIALogic::s_sort_integer = "Integer";

LIALogic::LIALogic(SMTConfig& c) :
      Logic(c)
    , sym_Int_ZERO(SymRef_Undef)
    , sym_Int_ONE(SymRef_Undef)
    , sym_Int_NEG(SymRef_Undef)
    , sym_Int_MINUS(SymRef_Undef)
    , sym_Int_PLUS(SymRef_Undef)
    , sym_Int_TIMES(SymRef_Undef)
    , sym_Int_DIV(SymRef_Undef)
    , sym_Int_EQ(SymRef_Undef)
    , sym_Int_LEQ(SymRef_Undef)
    , sym_Int_LT(SymRef_Undef)
    , sym_Int_GEQ(SymRef_Undef)
    , sym_Int_GT(SymRef_Undef)
    , sym_Int_ITE(SymRef_Undef)
    , sort_INTEGER(SRef_Undef)
    , term_Int_ZERO(PTRef_Undef)
    , term_Int_ONE(PTRef_Undef)
    , split_eq(false)
{
    char* m;
    char** msg = &m;

    logic_type = QF_LIA;

    sort_INTEGER = declareSort(s_sort_integer, msg);
    ufsorts.remove(sort_INTEGER);
//    printf("Setting sort_REAL to %d at %p\n", sort_REAL.x, &(sort_REAL.x));
    vec<SRef> params;


    term_Int_ZERO = mkConst(sort_INTEGER, tk_int_zero);
    sym_Int_ZERO  = getSymRef(term_Int_ZERO);
    sym_store.setInterpreted(sym_Int_ZERO);
    term_Int_ONE  = mkConst(sort_INTEGER, tk_int_one);
    sym_Int_ONE   = getSymRef(term_Int_ONE);
    sym_store.setInterpreted(sym_Int_ONE);


    params.push(sort_INTEGER);

    // Negation
    sym_Int_NEG = declareFun(tk_int_neg, sort_INTEGER, params, msg, true);
    sym_store.setInterpreted(sym_Int_NEG);

    params.push(sort_INTEGER);

    sym_Int_MINUS = declareFun(tk_int_neg, sort_INTEGER, params, msg, true);
    sym_store[sym_Int_MINUS].setLeftAssoc();
    sym_store.setInterpreted(sym_Int_MINUS);

    sym_Int_PLUS  = declareFun(tk_int_plus, sort_INTEGER, params, msg, true);
    sym_store[sym_Int_PLUS].setNoScoping();
    sym_store[sym_Int_PLUS].setCommutes();
    sym_store[sym_Int_PLUS].setLeftAssoc();
    sym_store.setInterpreted(sym_Int_PLUS);

    sym_Int_TIMES = declareFun(tk_int_times, sort_INTEGER, params, msg, true);
    sym_store[sym_Int_TIMES].setNoScoping();
    sym_store[sym_Int_TIMES].setLeftAssoc();
    sym_store[sym_Int_TIMES].setCommutes();
    sym_store.setInterpreted(sym_Int_TIMES);

    sym_Int_DIV   = declareFun(tk_int_div, sort_INTEGER, params, msg, true);
    sym_store[sym_Int_DIV].setNoScoping();
    sym_store[sym_Int_DIV].setLeftAssoc();
    sym_store.setInterpreted(sym_Int_DIV);

    sym_Int_LEQ  = declareFun(tk_int_leq, sort_BOOL, params, msg, true);
    sym_store[sym_Int_LEQ].setNoScoping();
    sym_store[sym_Int_LEQ].setChainable();
    sym_store.setInterpreted(sym_Int_LEQ);

    sym_Int_LT   = declareFun(tk_int_lt, sort_BOOL, params, msg, true);
    sym_store[sym_Int_LT].setNoScoping();
    sym_store[sym_Int_LT].setChainable();
    sym_store.setInterpreted(sym_Int_LT);

    sym_Int_GEQ  = declareFun(tk_int_geq, sort_BOOL, params, msg, true);
    sym_store[sym_Int_GEQ].setNoScoping();
    sym_store[sym_Int_GEQ].setChainable();
    sym_store.setInterpreted(sym_Int_GEQ);

    sym_Int_GT   = declareFun(tk_int_gt, sort_BOOL, params, msg, true);
    sym_store[sym_Int_GT].setNoScoping();
    sym_store[sym_Int_GT].setChainable();
    sym_store.setInterpreted(sym_Int_GEQ);

    vec<SRef> ite_params;
    ite_params.push(sort_BOOL);
    ite_params.push(sort_INTEGER);
    ite_params.push(sort_INTEGER);
    sym_Int_ITE = declareFun(tk_ite, sort_INTEGER, ite_params, msg, true);
    //sym_store[sym_Real_ITE].setLeftAssoc();
    sym_store[sym_Int_ITE].setNoScoping();
    sym_store.setInterpreted(sym_Int_ITE);
}

bool LIALogic::isBuiltinFunction(const SymRef sr) const
{
    if (sr == sym_Int_NEG || sr == sym_Int_MINUS || sr == sym_Int_PLUS || sr == sym_Int_TIMES || sr == sym_Int_DIV || sr == sym_Int_EQ || sr == sym_Int_LEQ || sr == sym_Int_LT || sr == sym_Int_GEQ || sr == sym_Int_GT || sr == sym_Int_ITE) return true;
    else return Logic::isBuiltinFunction(sr);
}

const opensmt::Integer&
LIALogic::getIntegerConst(PTRef tr) const
{
    SymId id = sym_store[getPterm(tr).symb()].getId();
    assert(id < integers.size() && integers[id] != NULL);
    return *integers[id];
}

PTRef
LIALogic::mkConst(const char *name, const char **msg)
{
    return mkConst(getSort_integer(), name);
}

PTRef LIALogic::mkConst(SRef s, const char* name)
{
    assert(strlen(name) != 0);
    PTRef ptr = PTRef_Undef;
    if (s == sort_INTEGER) {
        char* rat;
        opensmt::stringToInteger(rat, name);
        ptr = mkVar(s, rat);
        // Store the value of the number as a real, and we need to store it as Integer?
        SymId id = sym_store[getPterm(ptr).symb()].getId();
        for (int i = integers.size(); i <= id; i++)
            integers.push(NULL);
        if (integers[id] != NULL) { delete integers[id]; }
        integers[id] = new opensmt::Integer(rat);
        free(rat);
        // Code to allow efficient constant detection.
        while (id >= constants.size())
            constants.push(false);
        constants[id] = true;
    } else
        ptr = Logic::mkConst(s, name);

    return ptr;
}

bool LIALogic::isIntegerTerm(PTRef tr) const
{
    const Pterm& t = getPterm(tr);
    if (t.size() == 2 && isIntTimes(tr))
        return ((isIntVar(t[0]) || isUF(t[0])) && isConstant(t[1])) || ((isIntVar(t[1]) || isUF(t[1])) && isConstant(t[0]));
    else if (t.size() == 0)
        return isIntVar(tr) || isConstant(tr);
    else
        return false;
}

bool
LIALogic::okForBoolVar(PTRef tr) const
{
    return isIntLeq(tr) || Logic::okForBoolVar(tr);
}

PTRef
LIALogic::insertTerm(SymRef sym, vec<PTRef>& terms, char **msg)
{
    if (sym == sym_Int_NEG)
        return mkIntNeg(terms[0], msg);
    if (sym == sym_Int_MINUS)
        return mkIntMinus(terms, msg);
    if (sym == sym_Int_PLUS)
        return mkIntPlus(terms, msg);
    if (sym == sym_Int_TIMES)
        return mkIntTimes(terms, msg);
    if (sym == sym_Int_DIV)
        return mkIntDiv(terms, msg);
    if (sym == sym_Int_LEQ)
        return mkIntLeq(terms, msg);
    if (sym == sym_Int_LT)
        return mkIntLt(terms, msg);
    if (sym == sym_Int_GEQ)
        return mkIntGeq(terms, msg);
    if (sym == sym_Int_GT)
        return mkIntGt(terms, msg);
    if (sym == sym_Int_ITE)
        return mkIte(terms);

    return Logic::insertTerm(sym, terms, msg);
}

PTRef LIALogic::mkIntNeg(PTRef tr, char** msg)
{
    if (isIntNeg(tr)) return getPterm(tr)[0];
    vec<PTRef> args;
    if (isIntPlus(tr)) {
        for (int i = 0; i < getPterm(tr).size(); i++) {
            PTRef tr_arg = mkIntNeg(getPterm(tr)[i], msg);
            assert(tr_arg != PTRef_Undef);
            args.push(tr_arg);
        }
        PTRef tr_n = mkIntPlus(args, msg);
        assert(tr_n != PTRef_Undef);
        return tr_n;
    }
    if (isConstant(tr)) {
        char* rat_str;
        opensmt::stringToInteger(rat_str, sym_store.getName(getPterm(tr).symb()));
        opensmt::Integer v(rat_str);
        free(rat_str);
        v = -v;
        PTRef nterm = mkConst(getSort_integer(), v.get_str().c_str());
        SymRef s = getPterm(nterm).symb();
        return mkFun(s, args, msg);
    }
    PTRef mo = mkConst(getSort_integer(), "-1");
    args.push(mo); args.push(tr);
    return mkIntTimes(args);
}

PTRef LIALogic::mkIntMinus(const vec<PTRef>& args_in, char** msg)
{
    SymRef s;
    vec<PTRef> args;
    args_in.copyTo(args);

    if (args.size() == 1) {
        return mkIntNeg(args[0], msg);
//        s = sym_Real_NEG;
//        return mkFun(s, args, msg);
    }
    assert (args.size() == 2);
    PTRef mo = mkConst(getSort_integer(), "-1");
    if (mo == PTRef_Undef) {
        printf("Error: %s\n", *msg);
        assert(false);
    }
    vec<PTRef> tmp;
    tmp.push(mo);
    tmp.push(args[1]);
    PTRef fact = mkIntTimes(tmp, msg);
    if (fact == PTRef_Undef) {
        printf("Error: %s\n", *msg);
        assert(false);
    }
    args[1] = fact;
    return mkIntPlus(args);
}

PTRef LIALogic::mkIntPlus(const vec<PTRef>& args, char** msg)
{
    vec<PTRef> new_args;

    // Flatten possible internal sums.  This needs not be done properly,
    // with a post-order dfs, since we are guaranteed that the inner
    // sums are already flattened.
    for (int i = 0; i < args.size(); i++) {
        if (isIntPlus(args[i])) {
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
    simp.simplify(sym_Int_PLUS, tmp_args, s_new, args_new, msg);
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
            c = getTerm_IntOne();
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
        PTRef consts_summed = mkIntPlus(consts);
        vec<PTRef> term_args;
        term_args.push(consts_summed);
        if (keys[i] != PTRef_Undef)
            term_args.push(keys[i]);
        else term_args.push(getTerm_IntOne());
        PTRef term = mkIntTimes(term_args);
        if (!isIntZero(term))
            sum_args.push(term);
    }

    if (sum_args.size() == 1) return sum_args[0];
    PTRef tr = mkFun(s_new, sum_args, msg);
//    PTRef tr = mkFun(s_new, args_new, msg);
    return tr;
}

PTRef LIALogic::mkIntTimes(const vec<PTRef>& tmp_args, char** msg)
{
    vec<PTRef> args;
    // Flatten possible internal multiplications
    for (int i = 0; i < tmp_args.size(); i++) {
        if (isIntTimes(tmp_args[i])) {
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
    simp.simplify(sym_Int_TIMES, args, s_new, args_new, msg);
    PTRef tr = mkFun(s_new, args_new, msg);
    // Either a real term or, if we constructed a multiplication of a
    // constant and a sum, a real sum.
    if (isIntTerm(tr) || isIntPlus(tr) || isUF(tr))
        return tr;
    else {
        char* err;
        asprintf(&err, "%s", printTerm(tr));
        throw LIANonLinearException(err);
    }
}

PTRef LIALogic::mkIntDiv(const vec<PTRef>& args, char** msg)
{
    SimplifyConstDiv simp(*this);
    vec<PTRef> args_new;
    SymRef s_new;

    simp.simplify(sym_Int_DIV, args, s_new, args_new, msg);
    assert(args.size() == 2);

//how to be with FastRational_inverse function? Do we need to create one for Integer? Or this needs to be ommitted as for integers revers will no longer be integer?
    if (isIntDiv(s_new)) {
        assert(isIntTerm(args_new[0]) && isConstant(args_new[1]));
        args_new[1] = mkConst(FastRational_inverse(getIntegerConst(args_new[1]))); //mkConst(1/getRealConst(args_new[1]));
        return mkIntTimes(args_new);
    }

    PTRef tr = mkFun(s_new, args_new, msg);
    return tr;
}

// Find the lexicographically first factor of a term and divide the other terms with it.
PTRef LIALogic::normalizeSum(PTRef sum) {
    vec<PTRef> args;
    Pterm& s = getPterm(sum);
    for  (int i = 0; i < s.size(); i++)
        args.push(s[i]);
    termSort(args);
    PTRef const_term = PTRef_Undef;
    for (int i = 0; i < args.size(); i++) {
        if (isIntVar(args[i])) {
            // The lex first term has an implicit unit factor, no need to do anything.
            return sum;
        }
        if (isIntTimes(args[i])) {
            assert(!isIntZero(getPterm(args[i])[0]) && !isIntZero(getPterm(args[i])[1]));
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
    opensmt::Integer k = abs(isConstant(t[0]) ? getIntegerConst(t[0]) : getIntegerConst(t[1]));
    PTRef divisor = mkConst(k);
    for (int i = 0; i < args.size(); i++) {
        vec<PTRef> tmp;
        tmp.push(args[i]);
        tmp.push(divisor);
        args[i] = mkIntDiv(tmp);
    }
    return mkIntPlus(args);
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
bool LIALogic::isNegated(PTRef tr) const {
    if (isIntegerConst(tr))
        return getIntegerConst(tr) < 0; // Case (0a) and (0b)
    if (isIntVar(tr))
        return false; // Case (1a)
    if (isIntTimes(tr)) {
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

void LIALogic::splitTermToVarAndConst(const PTRef& term, PTRef& var, PTRef& fac) const
{
    assert(isIntTimes(term) || isIntDiv(term) || isIntVar(term) || isConstant(term) || isUF(term));
    if (isIntTimes(term) || isIntDiv(term)) {
        assert(getPterm(term).size() == 2);
        fac = getPterm(term)[0];
        var = getPterm(term)[1];
        if (!isConstant(fac)) {
            PTRef t = var;
            var = fac;
            fac = t;
        }
        assert(isConstant(fac));
        assert(isIntVar(var) || isUF(var));
    } else if (isIntVar(term) || isUF(term)) {
        var = term;
        fac = getTerm_IntOne();
    } else {
        var = getTerm_IntOne();
        fac = term;
    }
}


// Normalize a product of the form (* a v) to either v or (* -1 v)
PTRef LIALogic::normalizeMul(PTRef mul)
{
    assert(isIntTimes(mul));
    PTRef v = PTRef_Undef;
    PTRef c = PTRef_Undef;
    splitTermToVarAndConst(mul, v, c);
    opensmt::Integer r = getIntConst(c);
    if (r < 0)
        return mkIntNeg(v);
    else
        return v;
}

// If the call results in a leq it is guaranteed that arg[0] is a
// constant, and arg[1][0] has factor 1 or -1
PTRef LIALogic::mkIntLeq(const vec<PTRef>& args_in, char** msg)
{
    vec<PTRef> args;
    args_in.copyTo(args);
    assert(args.size() == 2);

    if (isConstant(args[0]) && isConstant(args[1])) {
        opensmt::Integer v1(sym_store.getName(getPterm(args[0]).symb()));
        opensmt::Integer v2(sym_store.getName(getPterm(args[1]).symb()));
        if (v1 <= v2)
            return getTerm_true();
        else
            return getTerm_false();

    } else {

        // Should be in the form that on one side there is a constant
        // and on the other there is a sum
        PTRef tr_neg = mkIntNeg(args[0], msg);
        vec<PTRef> sum_args;
        sum_args.push(args[1]);
        sum_args.push(tr_neg);
        PTRef sum_tmp = mkIntPlus(sum_args, msg); // This gives us a collapsed version of the sum
        if (isConstant(sum_tmp)) {
            args[0] = getTerm_IntZero();
            args[1] = sum_tmp;
            return mkIntLeq(args, msg); // either true or false
        } if (isIntTimes(sum_tmp)) {
            sum_tmp = normalizeMul(sum_tmp);
        } else if (isIntPlus(sum_tmp)) {
            // Normalize the sum
            sum_tmp = normalizeSum(sum_tmp); //Now the sum is normalized by dividing with the "first" factor.
        }
        // Otherwise no operation, already normalized

        vec<PTRef> nonconst_args;
        PTRef c = PTRef_Undef;
        if (isIntPlus(sum_tmp)) {
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
                args[0] = getTerm_IntZero();
                args[1] = mkIntPlus(nonconst_args);
            } else {
                args[0] = mkIntNeg(c);
                args[1] = mkIntPlus(nonconst_args);
            }
        } else if (isIntVar(sum_tmp) || isIntTimes(sum_tmp)) {
            args[0] = getTerm_IntZero();
            args[1] = sum_tmp;
        } else assert(false);

        PTRef r = mkFun(sym_Int_LEQ, args, msg);
        return r;
    }
}

PTRef LIALogic::mkIntGeq(const vec<PTRef>& args, char** msg)
{
    vec<PTRef> new_args;
    new_args.push(args[1]);
    new_args.push(args[0]);
    return mkIntLeq(new_args, msg);
}

PTRef LIALogic::mkIntLt(const vec<PTRef>& args, char** msg)
{
    if (isConstant(args[0]) && isConstant(args[1])) {
        char *rat_str1, *rat_str2;
        opensmt::stringToInteger(rat_str1, sym_store.getName(getPterm(args[0]).symb()));
        opensmt::stringToInteger(rat_str2, sym_store.getName(getPterm(args[1]).symb()));
        opensmt::Integer v1(rat_str1);
        opensmt::Integer v2(rat_str2);
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
    PTRef tr = mkIntLeq(tmp, msg);
    if (tr == PTRef_Undef) {
        printf("%s\n", *msg);
        assert(false);
    }
    return mkNot(tr);
}

PTRef LIALogic::mkIntGt(const vec<PTRef>& args, char** msg)
{
    if (isConstant(args[0]) && isConstant(args[1])) {
        char *rat_str1, *rat_str2;
        opensmt::stringToInteger(rat_str1, sym_store.getName(getPterm(args[0]).symb()));
        opensmt::stringToIntegerl(rat_str2, sym_store.getName(getPterm(args[1]).symb()));
        opensmt::Integer v1(rat_str1);
        opensmt::Integer v2(rat_str2);
        free(rat_str1);
        free(rat_str2);
        if (v1 > v2)
            return getTerm_true();
        else
            return getTerm_false();
    }
    PTRef tr = mkIntLeq(args, msg);
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
    opensmt::Integer s = getIdOp();
    if (terms.size() == 0) {
        opensmt::Integer s = getIdOp();
        return l.mkConst(l.getSort_integer(), s.get_str().c_str());
    } else if (terms.size() == 1) {
        char* rat_str;
        opensmt::stringToInteger(rat_str, l.getSymName(terms[0]));
        opensmt::Integer val(rat_str);
        free(rat_str);
        return l.mkConst(l.getSort_integer(), val.get_str().c_str());
    } else {
        char* rat_str;
        opensmt::stringToInteger(rat_str, l.getSymName(terms[0]));
        opensmt::Integer s(rat_str);
        free(rat_str);
        for (int i = 1; i < terms.size(); i++) {
            PTRef tr = PTRef_Undef;
            if (l.isConstant(terms[i]))
                tr = terms[i];
            else if (l.isIntNeg(terms[i]))
                tr = l.getPterm(terms[i])[0];
            else continue;
            char* rat_str;
            opensmt::stringToInteger(rat_str, l.getSymName(tr));

            opensmt::Integer val(rat_str);
            free(rat_str);
            Op(s, val);
        }
        return l.mkConst(l.getSort_integer(), s.get_str().c_str());
    }
}

lbool LIALogic::retrieveSubstitutions(vec<PtAsgn>& facts, Map<PTRef,PtAsgn,PTRefHash>& substs)
{
    lbool res = Logic::retrieveSubstitutions(facts, substs);
    if (res != l_Undef) return res;
    vec<PTRef> top_level_arith;
    for (int i = 0; i < facts.size(); i++) {
        PTRef tr = facts[i].tr;
        lbool sgn = facts[i].sgn;
        if (isIntEq(tr) && sgn == l_True)
            top_level_arith.push(tr);
    }

    return arithmeticElimination(top_level_arith, substs);
}

//below code requires some changes in LA.h file I guess (LIALogic I think needs to be added)?
lbool LIALogic::arithmeticElimination(vec<PTRef> &top_level_arith, Map<PTRef,PtAsgn,PTRefHash>& substitutions)
{
    vec<LAExpression*> equalities;
    LIALogic& logic = *this;
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
void LIALogic::serializeLogicData(int*& logicdata_buf) const
{
    Logic::serializeLogicData(logicdata_buf);
    vec<SymRef> integer_syms;
    for (int i = 0; i < integers.size(); i++)
        if (integers[i] != NULL)
            integer_syms.push(sym_store.symbols[i]);

#ifdef VERBOSE_FOPS
    printf("Found %d integer symbols\n", integer_syms.size());
#endif
    int size_old = logicdata_buf[buf_sz_idx];
    int size_new = size_old + integer_syms.size() + 2;
    logicdata_buf = (int*) realloc(logicdata_buf, size_new*sizeof(int));
    logicdata_buf[size_old] = integer_syms.size();
    for (int i = 0; i < integer_syms.size(); i++)
        logicdata_buf[size_old+1+i] = integer_syms[i].x;
    logicdata_buf[buf_sz_idx] = size_new;
}

void LIALogic::deserializeLogicData(const int* logicdata_buf)
{
    Logic::deserializeLogicData(logicdata_buf);
    int mydata_init = logicdata_buf[constants_offs_idx] + logicdata_buf[logicdata_buf[constants_offs_idx]];
    assert(mydata_init < logicdata_buf[0]); // Inside the buffer still
    int sz = logicdata_buf[mydata_init];
    for (int i = 0; i < sz; i++) {
        SymRef sr = {(uint32_t) logicdata_buf[mydata_init+1+i]};
        SymId id = sym_store[sr].getId();
        for (int j = integers.size(); j <= id; j++)
            integers.push(NULL);
        integers[id] = new opensmt::integer(sym_store.idToName[id]);
        while (id >= constants.size())
            constants.push(false);
        constants[id] = true;
    }
}

//do I need to do any changes in below code? as in case of integers den should always be equal to 1

// Handle the printing of real constants that are negative and the
// rational constants
char*
LIALogic::printTerm_(PTRef tr, bool ext, bool safe) const
{
    char* out;
    if (isIntegerConst(tr))
    {
        bool is_neg = false;
        char* tmp_str;
        opensmt::stringToInteger(tmp_str, sym_store.getName(getPterm(tr).symb()));
        opensmt::Integer v(tmp_str);
        if (!isNonnegIntegerConst(tr))
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
