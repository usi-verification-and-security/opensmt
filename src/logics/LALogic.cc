#include "SStore.h"
#include "PtStore.h"
#include "TreeOps.h"
#include "StringConv.h"
#include "LA.h"
#include "LALogic.h"
#include "FastRational.h"
#include "OsmtInternalException.h"
#include "OsmtApiException.h"

#include <memory>

bool LALogic::isLinearFactor(PTRef tr) const {
    if (isNumConst(tr) || isNumVarLike(tr)) { return true; }
    if (isNumTimes(tr)) {
        Pterm const& term = getPterm(tr);
        return term.size() == 2 && ((isNumConst(term[0]) && (isNumVarLike(term[1])))
                                    || (isNumConst(term[1]) && (isNumVarLike(term[0]))));
    }
    return false;
}

bool LALogic::isLinearTerm(PTRef tr) const {
    if (isLinearFactor(tr)) { return true; }
    if (isNumPlus(tr)) {
        Pterm const& term = getPterm(tr);
        for (int i = 0; i < term.size(); ++i) {
            if (!isLinearFactor(term[i])) { return false; }
        }
        return true;
    }
    return false;
}

const opensmt::Number&
LALogic::getNumConst(PTRef tr) const
{
    SymId id = sym_store[getPterm(tr).symb()].getId();
    assert(id < static_cast<unsigned int>(numbers.size()) && numbers[id] != nullptr);
    return *numbers[id];
}

std::pair<opensmt::Number, vec<PTRef>> LALogic::getConstantAndFactors(PTRef sum) {
    assert(isNumPlus(sum));
    vec<PTRef> varFactors;
    PTRef constant = PTRef_Undef;
    Pterm const & s = getPterm(sum);
    for (PTRef arg : s) {
        if (isConstant(arg)) {
            assert(constant == PTRef_Undef);
            constant = arg;
        } else {
            assert(isLinearFactor(arg));
            varFactors.push(arg);
        }
    }
    if (constant == PTRef_Undef) { constant = getTerm_NumZero(); }
    auto constantValue = getNumConst(constant);
    assert(varFactors.size() > 0);
    termSort(varFactors);
    return std::pair(std::move(constantValue), std::move(varFactors));
}

void LALogic::splitTermToVarAndConst(const PTRef& term, PTRef& var, PTRef& fac) const
{
    assert(isNumTimes(term) || isNumVarLike(term) || isConstant(term));
    if (isNumTimes(term)) {
        assert(getPterm(term).size() == 2);
        fac = getPterm(term)[0];
        var = getPterm(term)[1];
        if (!isConstant(fac)) {
            PTRef t = var;
            var = fac;
            fac = t;
        }
        assert(isConstant(fac));
        assert(isNumVarLike(var));
    } else if (isNumVarLike(term)) {
        var = term;
        fac = getTerm_NumOne();
    } else {
        var = PTRef_Undef; // MB: no variable
        fac = term;
    }
}

// Normalize a product of the form (* a v) to either v or (* -1 v)
PTRef LALogic::normalizeMul(PTRef mul)
{
    assert(isNumTimes(mul));
    PTRef v = PTRef_Undef;
    PTRef c = PTRef_Undef;
    splitTermToVarAndConst(mul, v, c);
    if (getNumConst(c).sign() < 0) {
        return mkNumNeg(v);
    } else {
        return v;
    }
}
lbool LALogic::arithmeticElimination(const vec<PTRef> & top_level_arith, SubstMap & substitutions)
{
    std::vector<std::unique_ptr<LAExpression>> equalities;
    LALogic& logic = *this;
    // I don't know if reversing the order makes any sense but osmt1
    // does that.
    for (int i = top_level_arith.size() - 1; i >= 0; i--) {
        equalities.emplace_back(new LAExpression(logic, top_level_arith[i]));
    }

    for (auto const& equality : equalities) {
        PTRef res = equality->solve();
        if (res == PTRef_Undef) { // MB: special case where the equality simplifies to "c = 0" with c constant
            // This is a conflicting equality unless the constant "c" is also 0.
            // We do nothing here and let the main code deal with this
            continue;
        }
        auto sub = equality->getSubst();
        PTRef var = sub.first;
        assert(var != PTRef_Undef and isNumVarLike(var) and sub.second != PTRef_Undef);
        if (substitutions.has(var)) {
            // Already has substitution for this var, let the main substitution code deal with this situation
            continue;
        } else {
            substitutions.insert(var, sub.second);
        }
    }
    // To simplify this method, we do not try to detect a conflict here, so result is always l_Undef
    return l_Undef;
}

opensmt::pair<lbool,Logic::SubstMap> LALogic::retrieveSubstitutions(const vec<PtAsgn>& facts)
{
    auto resAndSubsts = Logic::retrieveSubstitutions(facts);
    if (resAndSubsts.first != l_Undef) return resAndSubsts;
    vec<PTRef> top_level_arith;
    for (int i = 0; i < facts.size(); i++) {
        PTRef tr = facts[i].tr;
        lbool sgn = facts[i].sgn;
        if (isNumEq(tr) && sgn == l_True)
            top_level_arith.push(tr);
    }
    lbool res = arithmeticElimination(top_level_arith, resAndSubsts.second);
    return {res, std::move(resAndSubsts.second)};
}

uint32_t LessThan_deepPTRef::getVarIdFromProduct(PTRef tr) const {
    assert(l.isNumTimes(tr));
    PTRef c_t;
    PTRef v_t;
    l.splitTermToVarAndConst(tr, v_t, c_t);
    return v_t.x;
}

bool LessThan_deepPTRef::operator()(PTRef x_, PTRef y_) const {
    uint32_t id_x = l.isNumTimes(x_) ? getVarIdFromProduct(x_) : x_.x;
    uint32_t id_y = l.isNumTimes(y_) ? getVarIdFromProduct(y_) : y_.x;
    return id_x < id_y;
}

void LALogic::termSort(vec<PTRef>& v) const
{
    sort(v, LessThan_deepPTRef(this));
}

bool LALogic::isBuiltinFunction(const SymRef sr) const
{
    if (sr == get_sym_Num_NEG() || sr == get_sym_Num_MINUS() || sr == get_sym_Num_PLUS() || sr == get_sym_Num_TIMES() || sr == get_sym_Num_EQ() || sr == get_sym_Num_LEQ() || sr == get_sym_Num_LT() || sr == get_sym_Num_GEQ() || sr == get_sym_Num_GT() || sr == get_sym_Num_ITE()) return true;
    else return Logic::isBuiltinFunction(sr);
}
bool LALogic::isNumTerm(PTRef tr) const
{
    if (isNumVarLike(tr))
        return true;
    const Pterm& t = getPterm(tr);
    if (t.size() == 2 && isNumTimes(tr))
        return (isNumVarLike(t[0]) && isConstant(t[1])) || (isNumVarLike(t[1]) && isConstant(t[0]));
    else if (t.size() == 0)
        return isNumVar(tr) || isConstant(tr);
    else
        return false;
}

PTRef LALogic::mkNumNeg(PTRef tr)
{
    assert(!isNumNeg(tr)); // MB: The invariant now is that there is no "Minus" node
    if (isConstant(tr)) {
        const opensmt::Number& v = getNumConst(tr);
        opensmt::Number min = -v;
        PTRef nterm = mkConst(min);
        return nterm;
    }
    vec<PTRef> args;
    if (isNumPlus(tr)) {
        args.capacity(getPterm(tr).size());
        for (int i = 0; i < getPterm(tr).size(); ++i) {
            PTRef tr_arg = mkNumNeg(getPterm(tr)[i]);
            assert(tr_arg != PTRef_Undef);
            args.push(tr_arg);
        }
        PTRef tr_n = mkFun(get_sym_Num_PLUS(), std::move(args));
        assert(tr_n != PTRef_Undef);
        return tr_n;
    }
    PTRef mo = this->getTerm_NumMinusOne();
    args.push(mo); args.push(tr);
    return mkNumTimes(std::move(args));
}

PTRef  LALogic::mkConst(const opensmt::Number& c)
{
    std::string str = c.get_str(); // MB: I cannot store c.get_str().c_str() directly, since that is a pointer inside temporary object -> crash.
    const char * val = str.c_str();
    PTRef ptr = PTRef_Undef;
    ptr = mkVar(getSort_num(), val);
    // Store the value of the number as a real
    SymId id = sym_store[getPterm(ptr).symb()].getId();
    for (int i = numbers.size(); static_cast<unsigned int>(i) <= id; i++) { numbers.push(nullptr); }
    if (numbers[id] == nullptr) { numbers[id] = new opensmt::Number(val); }
    assert(c == *numbers[id]);
    markConstant(id);
    return ptr;
}

char* LALogic::printTerm(PTRef tr) const { return printTerm_(tr, false, false); }
char* LALogic::printTerm(PTRef tr, bool l, bool s) const { return printTerm_(tr, l, s); }
PTRef LALogic::mkNumMinus(vec<PTRef> && args)
{
    assert(args.size() > 0);
    if (args.size() == 1) {
        return mkNumNeg(args[0]);
    }
    assert(args.size() == 2);
    if (args.size() > 2) { throw OsmtApiException("Too many terms provided to LALogic::mkNumMinus"); }
    PTRef mo = getTerm_NumMinusOne();
    PTRef fact = mkNumTimes(mo, args[1]);
    assert(fact != PTRef_Undef);
    args[1] = fact;
    return mkNumPlus(std::move(args));
}

PTRef LALogic::mkNumPlus(vec<PTRef> && args)
{
    vec<PTRef> flattened_args;
    flattened_args.capacity(args.size());
    // Flatten possible internal sums.  This needs not be done properly,
    // with a post-order dfs, since we are guaranteed that the inner
    // sums are already flattened.
    for (int i = 0; i < args.size(); ++i) {
        if (isNumPlus(args[i])) {
            Pterm const & t = getPterm(args[i]);
            for (int j = 0; j < t.size(); j++)
                flattened_args.push(t[j]);
        } else {
            flattened_args.push(args[i]);
        }
    }
    SimplifyConstSum simp(*this);
    args.clear();
    SymRef s_new;
    simp.simplify(get_sym_Num_PLUS(), flattened_args, s_new, args);
    if (args.size() == 1)
        return args[0];
    if (s_new != get_sym_Num_PLUS()) {
        return mkFun(s_new, std::move(args));
    }
    // This code takes polynomials (+ (* v c1) (* v c2)) and converts them to the form (* v c3) where c3 = c1+c2
    VecMap<PTRef,PTRef,PTRefHash> s2t;
    vec<PTRef> keys;
    for (PTRef arg : args) {
        PTRef v;
        PTRef c;
        splitTermToVarAndConst(arg, v, c);
        assert(c != PTRef_Undef);
        assert(isConstant(c));
        if (!s2t.has(v)) {
            s2t.insert(v, {c});
            keys.push(v);
        } else
            s2t[v].push(c);
    }
    flattened_args.clear();
    for (PTRef key : keys) {
        const vec<PTRef>& consts = s2t[key];
        PTRef consts_summed = consts.size() == 1 ? consts[0] : mkNumPlus(consts);
        if (isNumZero(consts_summed)) { continue; }
        if (key == PTRef_Undef) {
            flattened_args.push(consts_summed);
            continue;
        }
        if (isNumOne(consts_summed)) {
            flattened_args.push(key);
            continue;
        }
        // default case, variable and constant (cannot be simplified)
        PTRef term = mkFun(get_sym_Num_TIMES(), {consts_summed, key});
        flattened_args.push(term);
    }
    if (flattened_args.size() == 0) return getTerm_NumZero();
    if (flattened_args.size() == 1) return flattened_args[0];
    PTRef tr = mkFun(s_new, std::move(flattened_args));
    return tr;
}

PTRef LALogic::mkNumTimes(vec<PTRef> && args)
{
    vec<PTRef> flatten_args;
    // Flatten possible internal multiplications
    for (PTRef arg : args) {
        if (isNumTimes(arg)) {
            Pterm const & t = getPterm(arg);
            for (PTRef child : t)
                flatten_args.push(child);
        } else {
            flatten_args.push(arg);
        }
    }
    SimplifyConstTimes simp(*this);
    args.clear();
    SymRef s_new;
    simp.simplify(get_sym_Num_TIMES(), flatten_args, s_new, args);
    PTRef tr = mkFun(s_new, std::move(args));
    // Either a real term or, if we constructed a multiplication of a
    // constant and a sum, a real sum.
    if (isNumTerm(tr) || isNumPlus(tr) || isUF(tr) || isIte(tr))
        return tr;
    else {
        throw LANonLinearException(printTerm(tr));
    }
}

// If the call results in a leq it is guaranteed that arg[0] is a
// constant, and arg[1][0] has factor 1 or -1
PTRef LALogic::mkBinaryLeq(PTRef lhs, PTRef rhs) {
    if (isConstant(lhs) && isConstant(rhs)) {
        opensmt::Number const & v1 = this->getNumConst(lhs);
        opensmt::Number const & v2 = this->getNumConst(rhs);
        return v1 <= v2 ? getTerm_true() : getTerm_false();
    }
    // Should be in the form that on one side there is a constant
    // and on the other there is a sum
    PTRef sum_tmp = lhs == getTerm_NumZero() ? rhs : rhs == getTerm_NumZero() ? mkNumNeg(lhs) : mkNumPlus(rhs, mkNumNeg(lhs));
    // "sum_tmp = rhs - lhs" so the inequality is "0 <= sum_tmp"
    if (isConstant(sum_tmp)) {
        opensmt::Number const & v = this->getNumConst(sum_tmp);
        return v.sign() < 0 ? getTerm_false() : getTerm_true();
    } if (isNumVarLike(sum_tmp) || isNumTimes(sum_tmp)) { // "sum_tmp = c * v", just scale to "v" or "-v" without changing the sign
        sum_tmp = isNumTimes(sum_tmp) ? normalizeMul(sum_tmp) : sum_tmp;
        return mkFun(get_sym_Num_LEQ(), {getTerm_NumZero(), sum_tmp});
    } else if (isNumPlus(sum_tmp)) {
        // Normalize the sum
        return sumToNormalizedInequality(sum_tmp);
    }
    assert(false);
    throw OsmtInternalException{"Unexpected situation in LALogic::mkNumLeq"};
}

PTRef LALogic::mkBinaryGeq(PTRef lhs, PTRef rhs) {
    return mkBinaryLeq(rhs, lhs);
}

PTRef LALogic::mkBinaryLt(PTRef lhs, PTRef rhs) {
    return mkNot(mkBinaryGeq(lhs, rhs));
}

PTRef LALogic::mkBinaryGt(PTRef lhs, PTRef rhs) {
    return mkNot(mkBinaryLeq(lhs, rhs));
}

PTRef LALogic::mkNumLeq(vec<PTRef> const & args) {
    if (args.size() < 2) { throw OsmtApiException("Too few arguments passed to LALogic::mkNumLeq"); }
    if (args.size() == 2) {
        return mkBinaryLeq(args[0], args[1]);
    }
    vec<PTRef> binaryInequalities;
    binaryInequalities.capacity(args.size() - 1);
    for (int i = 1; i < args.size(); ++i) {
        binaryInequalities.push(mkBinaryLeq(args[i - 1], args[i]));
    }
    return mkAnd(std::move(binaryInequalities));
}

PTRef LALogic::mkNumGeq(vec<PTRef> const & args) {
    if (args.size() < 2) { throw OsmtApiException("Too few arguments passed to LALogic::mkNumGeq"); }
    if (args.size() == 2) {
        return mkBinaryGeq(args[0], args[1]);
    }
    vec<PTRef> binaryInequalities;
    binaryInequalities.capacity(args.size() - 1);
    for (int i = 1; i < args.size(); ++i) {
        binaryInequalities.push(mkBinaryGeq(args[i - 1], args[i]));
    }
    return mkAnd(std::move(binaryInequalities));
}

PTRef LALogic::mkNumLt(vec<PTRef> const & args)
{
    if (args.size() < 2) { throw OsmtApiException("Too few arguments passed to LALogic::mkNumLt"); }
    if (args.size() == 2) {
        return mkBinaryLt(args[0], args[1]);
    }
    vec<PTRef> binaryInequalities;
    binaryInequalities.capacity(args.size() - 1);
    for (int i = 1; i < args.size(); ++i) {
        binaryInequalities.push(mkBinaryLt(args[i - 1], args[i]));
    }
    return mkAnd(std::move(binaryInequalities));
}

PTRef LALogic::mkNumGt(vec<PTRef> const & args)
{
    if (args.size() < 2) { throw OsmtApiException("Too few arguments passed to LALogic::mkNumGt"); }
    if (args.size() == 2) {
        return mkBinaryGt(args[0], args[1]);
    }
    vec<PTRef> binaryInequalities;
    binaryInequalities.capacity(args.size() - 1);
    for (int i = 1; i < args.size(); ++i) {
        binaryInequalities.push(mkBinaryGt(args[i - 1], args[i]));
    }
    return mkAnd(std::move(binaryInequalities));
}

PTRef LALogic::mkBinaryEq(PTRef lhs, PTRef rhs) {
    if (getSortRef(lhs) == getSort_num()) {
        assert(getSortRef(rhs) == getSort_num());
        if (isConstant(lhs) && isConstant(rhs)) {
            opensmt::Number const & v1 = this->getNumConst(lhs);
            opensmt::Number const & v2 = this->getNumConst(rhs);
            return v1 == v2 ? getTerm_true() : getTerm_false();
        }
        // diff = rhs - lhs
        PTRef diff = lhs == getTerm_NumZero() ? rhs : rhs == getTerm_NumZero() ? mkNumNeg(lhs) : mkNumPlus(rhs, mkNumNeg(lhs));
        if (isConstant(diff)) {
            opensmt::Number const & v = this->getNumConst(diff);
            return v.isZero() ? getTerm_true() : getTerm_false();
        } if (isNumVarLike(diff) || isNumTimes(diff)) {
            PTRef var, constant;
            splitTermToVarAndConst(diff, var, constant);
            return mkFun(get_sym_Num_EQ(), {getTerm_NumZero(), var});
        } else if (isNumPlus(diff)) {
            return sumToNormalizedEquality(diff);
        }
        assert(false);
        throw OsmtInternalException{"Unexpected situation in LALogic::mkNumLeq"};
    }
    return Logic::mkBinaryEq(lhs, rhs);
}

PTRef LALogic::insertTerm(SymRef sym, vec<PTRef> && terms)
{
    if (sym == get_sym_Num_NEG())
        return mkNumNeg(terms[0]);
    if (sym == get_sym_Num_MINUS())
        return mkNumMinus(std::move(terms));
    if (sym == get_sym_Num_PLUS())
        return mkNumPlus(std::move(terms));
    if (sym == get_sym_Num_TIMES())
        return mkNumTimes(std::move(terms));
    if (sym == get_sym_Num_LEQ())
        return mkNumLeq(std::move(terms));
    if (sym == get_sym_Num_LT())
        return mkNumLt(std::move(terms));
    if (sym == get_sym_Num_GEQ())
        return mkNumGeq(std::move(terms));
    if (sym == get_sym_Num_GT())
        return mkNumGt(std::move(terms));
    if (sym == get_sym_Num_ITE())
        return mkIte(std::move(terms));
    return Logic::insertTerm(sym, std::move(terms));
}

PTRef LALogic::mkConst(SRef s, const char* name)
{
    assert(strlen(name) != 0);
    PTRef ptr = PTRef_Undef;
    if (s == get_sort_Num()) {
        char* rat;
        opensmt::stringToRational(rat, name);
        ptr = mkVar(s, rat);
        // Store the value of the number as a real
        SymId id = sym_store[getPterm(ptr).symb()].getId();
        for (int i = numbers.size(); static_cast<unsigned>(i) <= id; i++)
            numbers.push(nullptr);
        if (numbers[id] != nullptr) { delete numbers[id]; }
        numbers[id] = new opensmt::Number(rat);
        free(rat);
        markConstant(id);
    } else
        ptr = Logic::mkConst(s, name);
    return ptr;
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
void SimplifyConst::simplify(const SymRef& s, const vec<PTRef>& args, SymRef& s_new, vec<PTRef>& args_new)
{
    vec<int> const_idx;
    for (int i = 0; i < args.size(); i++) {
        assert(!l.isNumNeg(args[i])); // MB: No minus nodes, the check can be simplified
        if (l.isConstant(args[i])) {
            assert(not l.isIte(args[i]));
            const_idx.push(i);
        }
    }
    if (const_idx.size() == 0) {
        s_new = s;
        args.copyTo(args_new);
    }
    else {
        if (const_idx.size() > 1) {
            vec<PTRef> const_terms;
            for (int i = 0; i < const_idx.size(); i++)
                const_terms.push(args[const_idx[i]]);
            PTRef tr = simplifyConstOp(const_terms);
            assert(tr != PTRef_Undef);

            vec<PTRef> args_new_2;
            args_new_2.capacity((args.size() - const_terms.size()) + 1);
            int i, k;
            for (i = k = 0; k < const_terms.size(); i++) {
                if (i != const_idx[k]) { args_new_2.push(args[i]); }
                else { k++; }
            }
            // Copy also the rest
            for (; i < args.size(); i++) {
                args_new_2.push(args[i]);
            }
            args_new_2.push(tr);
            constSimplify(s, args_new_2, s_new, args_new);
        } else {
            constSimplify(s, args, s_new, args_new);
        }

    }
//    // A single argument for the operator, and the operator is identity
//    // in that case
    if (args_new.size() == 1 && (l.isNumPlus(s_new) || l.isNumTimes(s_new) )) {
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
        if (!l.isNumZero(terms[i]))
            terms_new.push(terms[i]);
    if (terms_new.size() == 0) {
        // The term was sum of all zeroes
        terms_new.clear();
        s_new = l.getPterm(l.getTerm_NumZero()).symb();
        return;
    }
    s_new = s;
}
void SimplifyConstTimes::constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const
{
    PTRef con, plus;
    con = plus = PTRef_Undef;
    for (int i = 0; i < terms.size(); i++) {
        if (l.isNumZero(terms[i])) {
            terms_new.clear();
            s_new = l.getPterm(l.getTerm_NumZero()).symb();
            return;
        }
        if (!l.isNumOne(terms[i]))
        {
            if (l.isNumPlus(terms[i])) {
                plus = terms[i];
            } else if (l.isConstant(terms[i])) {
                con = terms[i];
            } else {
                terms_new.push(terms[i]);
            }
        }
    }
    if (con == PTRef_Undef && plus == PTRef_Undef);
    else if(con == PTRef_Undef && plus != PTRef_Undef)
        terms_new.push(plus);
    else if (con != PTRef_Undef && plus == PTRef_Undef)
        terms_new.push(con);
    else
    {
        assert(con != PTRef_Undef && plus != PTRef_Undef);
        //distribute the constant over the sum
        vec<PTRef> sum_args;
        int termSize = l.getPterm(plus).size();
        for (int i = 0; i < termSize; ++i)
        {
            // MB: we cannot use Pterm& here, because in the line after next new term might be allocated, which might
            //     trigger reallocation of the table of terms
            PTRef arg = l.getPterm(plus)[i];
            sum_args.push(l.mkNumTimes(con, arg));
        }
        terms_new.push(l.mkNumPlus(std::move(sum_args)));
    }
    if (terms_new.size() == 0) {
        // The term was multiplication of all ones
        terms_new.clear();
        s_new = l.getPterm(l.getTerm_NumOne()).symb();
        return;
    }
    s_new = s;
}
void SimplifyConstDiv::constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const
{
    assert(terms_new.size() == 0);
    assert(terms.size() <= 2);
    if (terms.size() == 2 && l.isNumZero(terms[1])) {
        printf("Explicit div by zero\n");
        assert(false);
    }
    if (terms.size() == 1 or l.isNumOne(terms[terms.size()-1])) {
        terms_new.clear();
        s_new = l.getPterm(terms[0]).symb();
        for (int i = 0; i < l.getPterm(terms[0]).size(); i++)
            terms_new.push(l.getPterm(terms[0])[i]);
        return;
    }
    else if (l.isNumZero(terms[0])) {
        terms_new.clear();
        s_new = l.getPterm(terms[0]).symb();
        return;
    }
    for (int i = 0; i < terms.size(); i++)
        terms_new.push(terms[i]);
    s_new = s;
}
// Return a term corresponding to the operation applied to the constant
// terms.  The list may contain terms of the form (* -1 a) for constant
// a.
PTRef SimplifyConst::simplifyConstOp(const vec<PTRef> & terms)
{
    if (terms.size() == 0) {
        opensmt::Number s = getIdOp();
        return l.mkConst(s);
    } else if (terms.size() == 1) {
        return terms[0];
    } else {
        opensmt::Number s = l.getNumConst(terms[0]);
        for (int i = 1; i < terms.size(); i++) {
            assert(l.isConstant((terms[i])));
            opensmt::Number const& val = l.getNumConst(terms[i]);
            Op(s, val);
        }
        return l.mkConst(s);
    }
}
const char* LALogic::tk_val_num_default = "1";
const char* LALogic::tk_num_zero  = "0";
const char* LALogic::tk_num_one   = "1";
const char* LALogic::tk_num_neg   = "-";
const char* LALogic::tk_num_minus = "-";
const char* LALogic::tk_num_plus  = "+";
const char* LALogic::tk_num_times = "*";
const char* LALogic::tk_num_div   = "/";
const char* LALogic::tk_num_lt    = "<";
const char* LALogic::tk_num_leq   = "<=";
const char* LALogic::tk_num_gt    = ">";
const char* LALogic::tk_num_geq   = ">=";
const char* LALogic::s_sort_num = "Number";


const char*
LALogic::getDefaultValue(const PTRef tr) const
{
    if (hasSortNum(tr))
        return tk_val_num_default;
    else
        return Logic::getDefaultValue(tr);
}

PTRef
LALogic::getDefaultValuePTRef(const SRef sref) const
{
    if (sref == getSort_num())
        return getTerm_NumZero();
    else
        return Logic::getDefaultValuePTRef(sref);
}


// Handle the printing of real constants that are negative and the
// rational constants
char*
LALogic::printTerm_(PTRef tr, bool ext, bool safe) const
{
    char* out;
    if (isNumConst(tr))
    {
        bool is_neg = false;
        char* tmp_str;
        opensmt::stringToRational(tmp_str, sym_store.getName(getPterm(tr).symb()));
        opensmt::Number v(tmp_str);
        if (!isNonnegNumConst(tr))
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
                int written = is_neg ? asprintf(&out, "(/ (- %s) %s) <%d>", nom, den, tr.x)
                        : asprintf(&out, "(/ %s %s) <%d>", nom, den, tr.x);
                assert(written >= 0); (void)written;
            }
            else {
                int written = is_neg ? asprintf(&out, "(/ (- %s) %s)", nom, den)
                    : asprintf(&out, "(/ %s %s)", nom, den);
                assert(written >= 0); (void)written;
            }
            free(nom);
            free(den);
        }
        else if (is_neg) {
            int written = ext ? asprintf(&out, "(- %s) <%d>", rat_str, tr.x)
                    : asprintf(&out, "(- %s)", rat_str);
            assert(written >= 0); (void) written;
        }
        else
            out = rat_str;
    }
    else
        out = Logic::printTerm_(tr, ext, safe);
    return out;
}

PTRef LALogic::getConstantFromLeq(PTRef leq) {
    Pterm const & term = getPterm(leq);
    if (not isNumLeq(term.symb())) {
        throw OsmtApiException("LALogic::getConstantFromLeq called on a term that is not less-or-equal inequality");
    }
    return term[0];
}

PTRef LALogic::getTermFromLeq(PTRef leq) {
    Pterm const & term = getPterm(leq);
    if (not isNumLeq(term.symb())) {
        throw OsmtApiException("LALogic::getConstantFromLeq called on a term that is not less-or-equal inequality");
    }
    return term[1];
}

std::pair<PTRef, PTRef> LALogic::leqToConstantAndTerm(PTRef leq) {
    Pterm const & term = getPterm(leq);
    assert(isNumLeq(term.symb()));
    return std::make_pair(term[0], term[1]);
}

void SimplifyConstSum::Op(opensmt::Number& s, const opensmt::Number& v) const { s += v; }
opensmt::Number SimplifyConstSum::getIdOp() const { return 0; }
void SimplifyConstTimes::Op(opensmt::Number& s, const opensmt::Number& v) const { s *= v; }
opensmt::Number SimplifyConstTimes::getIdOp() const { return 1; }
void SimplifyConstDiv::Op(opensmt::Number& s, const opensmt::Number& v) const { if (v == 0) { printf("explicit div by zero\n"); } s /= v; }
opensmt::Number SimplifyConstDiv::getIdOp() const { return 1; }


