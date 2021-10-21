#include "SStore.h"
#include "PtStore.h"
#include "TreeOps.h"
#include "Global.h"
#include "LA.h"
#include "ArithLogic.h"
#include "FastRational.h"
#include "OsmtInternalException.h"
#include "OsmtApiException.h"
#include <memory>
const std::string ArithLogic::e_nonlinear_term = "Logic does not support nonlinear terms";

/***********************************************************
 * Class defining simplifications
 ***********************************************************/

const std::string ArithLogic::tk_int_zero  = "0";
const std::string ArithLogic::tk_int_one   = "1";
const std::string ArithLogic::tk_int_neg   = "-";
const std::string ArithLogic::tk_int_minus = "-";
const std::string ArithLogic::tk_int_plus  = "+";
const std::string ArithLogic::tk_int_times = "*";
const std::string ArithLogic::tk_int_ntimes= "*";
const std::string ArithLogic::tk_int_div   = "div";
const std::string ArithLogic::tk_int_mod   = "mod";
const std::string ArithLogic::tk_int_abs   = "abs";
const std::string ArithLogic::tk_int_lt    = "<";
const std::string ArithLogic::tk_int_leq   = "<=";
const std::string ArithLogic::tk_int_gt    = ">";
const std::string ArithLogic::tk_int_geq   = ">=";

const std::string ArithLogic::s_sort_int = "Int";

const std::string ArithLogic::tk_real_zero  = "0";
const std::string ArithLogic::tk_real_one   = "1";
const std::string ArithLogic::tk_real_neg   = "-";
const std::string ArithLogic::tk_real_minus = "-";
const std::string ArithLogic::tk_real_abs   = "abs";
const std::string ArithLogic::tk_real_plus  = "+";
const std::string ArithLogic::tk_real_times = "*";
const std::string ArithLogic::tk_real_ntimes= "*";
const std::string ArithLogic::tk_real_div   = "/";
const std::string ArithLogic::tk_real_ndiv  = "/";
const std::string ArithLogic::tk_real_lt    = "<";
const std::string ArithLogic::tk_real_leq   = "<=";
const std::string ArithLogic::tk_real_gt    = ">";
const std::string ArithLogic::tk_real_geq   = ">=";
const std::string ArithLogic::s_sort_real   = "Real";

const std::string ArithLogic::tk_val_int_default  = "0";
const std::string ArithLogic::tk_val_real_default = "0.0";

ArithLogic::ArithLogic(ArithType arithType)
    : Logic()

    , sort_REAL(declareSortAndCreateFunctions(s_sort_real))
    , term_Real_ZERO(mkConst(sort_REAL, tk_real_zero.c_str()))
    , term_Real_ONE(mkConst(sort_REAL, tk_real_one.c_str()))
    , term_Real_MINUSONE(mkConst(sort_REAL, tk_real_minus + tk_real_one))
    , sym_Real_ZERO(getSymRef(term_Real_ZERO))
    , sym_Real_ONE(getSymRef(term_Real_ONE))
    , sym_Real_NEG(declareFun_NoScoping(tk_real_neg, sort_REAL, {sort_REAL}))
    , sym_Real_MINUS(declareFun_NoScoping_LeftAssoc(tk_real_minus, sort_REAL, {sort_REAL, sort_REAL}))
    , sym_Real_ABS(declareFun_NoScoping(tk_real_abs, sort_REAL, {sort_REAL}))
    , sym_Real_PLUS(declareFun_Commutative_NoScoping_LeftAssoc(tk_real_plus, sort_REAL, {sort_REAL, sort_REAL}))
    , sym_Real_TIMES(declareFun_Commutative_NoScoping_LeftAssoc(tk_real_times, sort_REAL, {sort_REAL, sort_REAL}))
    , sym_Real_NTIMES(declareFun_Commutative_NoScoping_LeftAssoc(tk_real_ntimes, sort_REAL, {sort_REAL, sort_REAL}))
    , sym_Real_DIV(declareFun_NoScoping_LeftAssoc(tk_real_div, sort_REAL, {sort_REAL, sort_REAL}))
    , sym_Real_NDIV(declareFun_NoScoping_LeftAssoc(tk_real_ndiv, sort_REAL, {sort_REAL, sort_REAL}))
    , sym_Real_EQ(declareFun_Commutative_NoScoping_Chainable(tk_equals, sort_BOOL, {sort_REAL, sort_REAL}))
    , sym_Real_LEQ(declareFun_NoScoping_Chainable(tk_real_leq, sort_BOOL, {sort_REAL, sort_REAL}))
    , sym_Real_LT(declareFun_NoScoping_Chainable(tk_real_lt, sort_BOOL, {sort_REAL, sort_REAL}))
    , sym_Real_GEQ(declareFun_NoScoping_Chainable(tk_real_geq, sort_BOOL, {sort_REAL, sort_REAL}))
    , sym_Real_GT(declareFun_NoScoping_Chainable(tk_real_gt, sort_BOOL, {sort_REAL, sort_REAL}))
    , sym_Real_ITE(declareFun(tk_ite, sort_REAL, {sort_BOOL, sort_REAL, sort_REAL}, true))

    , sort_INT(declareSortAndCreateFunctions(s_sort_int))
    , term_Int_ZERO(mkConst(sort_INT, tk_int_zero))
    , term_Int_ONE(mkConst(sort_INT, tk_int_one.c_str()))
    , term_Int_MINUSONE(mkConst(sort_INT, tk_int_minus + tk_int_one))
    , sym_Int_ZERO(getSymRef(term_Int_ZERO))
    , sym_Int_ONE(getSymRef(term_Int_ONE))
    , sym_Int_NEG(declareFun_NoScoping(tk_int_neg, sort_INT, {sort_INT}))
    , sym_Int_MINUS(declareFun_NoScoping_LeftAssoc(tk_int_minus, sort_INT, {sort_INT, sort_INT}))
    , sym_Int_ABS(declareFun_NoScoping(tk_int_abs, sort_INT, {sort_INT}))
    , sym_Int_PLUS(declareFun_Commutative_NoScoping_LeftAssoc(tk_int_plus, sort_INT, {sort_INT, sort_INT}))
    , sym_Int_TIMES(declareFun_Commutative_NoScoping_LeftAssoc(tk_int_times, sort_INT, {sort_INT, sort_INT}))
    , sym_Int_NTIMES(declareFun_Commutative_NoScoping_LeftAssoc(tk_int_ntimes, sort_INT, {sort_INT, sort_INT}))
    , sym_Int_DIV(declareFun_NoScoping_LeftAssoc(tk_int_div, sort_INT, {sort_INT, sort_INT}))
    , sym_Int_NDIV(declareFun_NoScoping_LeftAssoc(tk_int_div, sort_INT, {sort_INT, sort_INT}))
    , sym_Int_MOD(declareFun_NoScoping(tk_int_mod, sort_INT, {sort_INT, sort_INT}))
    , sym_Int_NMOD(declareFun_NoScoping(tk_int_mod, sort_INT, {sort_INT, sort_INT}))
    , sym_Int_EQ(declareFun_Commutative_NoScoping_Chainable(tk_equals, sort_BOOL, {sort_INT, sort_INT}))
    , sym_Int_LEQ(declareFun_NoScoping_Chainable(tk_int_leq, sort_BOOL, {sort_INT, sort_INT}))
    , sym_Int_LT(declareFun_NoScoping_Chainable(tk_int_lt, sort_BOOL, {sort_INT, sort_INT}))
    , sym_Int_GEQ(declareFun_NoScoping_Chainable(tk_int_geq, sort_BOOL, {sort_INT, sort_INT}))
    , sym_Int_GT(declareFun_NoScoping_Chainable(tk_int_gt, sort_BOOL, {sort_INT, sort_INT}))
    , sym_Int_ITE(declareFun(tk_ite, sort_INT, {sort_BOOL, sort_INT, sort_INT}, true))

    , arithType(arithType)
    , logicNames({"LIA", "LRA", "NIA", "NRA", "LIRA", "NIRA", "DRL", "IDL"})
    , logicTypes({opensmt::Logic_t::QF_LIA, opensmt::Logic_t::QF_LRA, opensmt::Logic_t::QF_NIA,
                  opensmt::Logic_t::QF_NRA, opensmt::Logic_t::QF_LIRA, opensmt::Logic_t::QF_NIRA,
                  opensmt::Logic_t::QF_RDL, opensmt::Logic_t::QF_IDL})
    , defaultSorts({sort_INT, sort_REAL, sort_INT, sort_REAL, sort_INT, sort_INT, sort_REAL, sort_INT})
{
    assert((static_cast<int>(logicNames.size()) == logicTypes.size()) && (logicTypes.size() == defaultSorts.size()));
}

bool ArithLogic::isIntegralLogic() const {
    switch (arithType) {
        case ArithType::LIA:
        case ArithType::NIA:
        case ArithType::IDL:
            return true;
        default:
            return false;
    }
}

bool ArithLogic::isRealLogic() const {
    switch (arithType) {
        case ArithType::LRA:
        case ArithType::NRA:
            return true;
        default:
            return false;
    }
}

void ArithLogic::checkArithSortCompatibleAndDefined(PTRef tr) const {
    if (isIntegralLogic() and getSortRef(tr) != sort_INT) {
        throw OsmtApiException("Incompatible sort");
    } else if (isRealLogic() and getSortRef(tr) != sort_REAL) {
        throw OsmtApiException("Incompatible sort");
    } else if (not isIntegralLogic() and not isRealLogic()) {
        throw OsmtApiException("Sort not uniquely defined");
    }
}

SymRef ArithLogic::get_sym_Num_PLUS() const {
    checkArithSortDefined();
    return isIntegralLogic() ? sym_Int_PLUS : sym_Real_PLUS;
}

SymRef ArithLogic::get_sym_Num_MINUS() const {
    checkArithSortDefined();
    return isIntegralLogic() ? sym_Int_MINUS : sym_Real_MINUS;
}

const SymRef ArithLogic::get_sym_Num_NEG() const {
    checkArithSortDefined();
    return isIntegralLogic() ? sym_Int_NEG : sym_Real_NEG;
}

const SymRef ArithLogic::get_sym_Num_LEQ() const {
    checkArithSortDefined();
    return isIntegralLogic() ? sym_Int_LEQ : sym_Real_LEQ;
}

const SymRef ArithLogic::get_sym_Num_GEQ() const {
    checkArithSortDefined();
    return isIntegralLogic() ? sym_Int_GEQ : sym_Real_GEQ;
}

const SymRef ArithLogic::get_sym_Num_LT() const {
    checkArithSortDefined();
    return isIntegralLogic() ? sym_Int_LT : sym_Real_LT;
}

const SymRef ArithLogic::get_sym_Num_GT() const {
    checkArithSortDefined();
    return isIntegralLogic() ? sym_Int_GT : sym_Real_GT;
}

const SymRef ArithLogic::get_sym_Num_EQ() const {
    checkArithSortDefined();
    return isIntegralLogic() ? sym_Int_EQ: sym_Real_EQ;
}

const SymRef ArithLogic::get_sym_Num_ZERO() const {
    checkArithSortDefined();
    return isIntegralLogic() ? sym_Int_ZERO : sym_Real_ZERO;
}

const SymRef ArithLogic::get_sym_Num_ONE() const {
    checkArithSortDefined();
    return isIntegralLogic() ? sym_Int_ONE : sym_Real_ONE;
}

const SymRef ArithLogic::get_sym_Num_ITE() const {
    checkArithSortDefined();
    return isIntegralLogic() ? sym_Int_ITE : sym_Real_ITE;
}

const SymRef ArithLogic::get_sym_Num_ABS() const {
    checkArithSortDefined();
    return isIntegralLogic() ? sym_Int_ABS : sym_Real_ABS;
}

SymRef ArithLogic::get_sym_Num_TIMES() const {
    checkArithSortDefined();
    return isIntegralLogic() ? sym_Int_TIMES : sym_Real_TIMES;
}

SymRef ArithLogic::get_sym_Num_NTIMES() const {
    checkArithSortDefined();
    return isIntegralLogic() ? sym_Int_NTIMES : sym_Real_NTIMES;
}

bool ArithLogic::isNegated(PTRef tr) const {
    if (isNumConst(tr))
        return getNumConst(tr) < 0; // Case (0a) and (0b)
    if (isNumVar(tr))
        return false; // Case (1a)
    if (isNumTimes(tr)) {
        // Cases (2)
        PTRef v;
        PTRef c;
        splitTermToVarAndConst(tr, v, c);
        return isNegated(c);
    }
    if (isIte(tr)) {
        return false;
    }
    else {
        // Cases(3)
        return isNegated(getPterm(tr)[0]);
    }
}

bool ArithLogic::isLinearFactor(PTRef tr) const {
    if (isNumConst(tr) || isNumVarLike(tr)) { return true; }
    if (isNumTimes(tr)) {
        Pterm const& term = getPterm(tr);
        return term.size() == 2 && ((isNumConst(term[0]) && (isNumVarLike(term[1])))
                                    || (isNumConst(term[1]) && (isNumVarLike(term[0]))));
    }
    return false;
}

bool ArithLogic::isLinearTerm(PTRef tr) const {
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

const FastRational&
ArithLogic::getNumConst(PTRef tr) const
{
    SymId id = sym_store[getPterm(tr).symb()].getId();
    assert(id < static_cast<unsigned int>(numbers.size()) && numbers[id] != nullptr);
    return *numbers[id];
}

std::pair<opensmt::Number, vec<PTRef>> ArithLogic::getConstantAndFactors(PTRef sum) const {
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

void ArithLogic::splitTermToVarAndConst(PTRef term, PTRef& var, PTRef& fac) const
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
PTRef ArithLogic::normalizeMul(PTRef mul)
{
    assert(isNumTimes(mul));
    PTRef v = PTRef_Undef;
    PTRef c = PTRef_Undef;
    splitTermToVarAndConst(mul, v, c);
    if (getNumConst(c) < 0) {
        return mkNumNeg(v);
    } else {
        return v;
    }
}
lbool ArithLogic::arithmeticElimination(const vec<PTRef> & top_level_arith, SubstMap & substitutions)
{
    std::vector<std::unique_ptr<LAExpression>> equalities;
    ArithLogic& logic = *this;
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

opensmt::pair<lbool,Logic::SubstMap> ArithLogic::retrieveSubstitutions(const vec<PtAsgn>& facts)
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

void ArithLogic::termSort(vec<PTRef>& v) const
{
    sort(v, LessThan_deepPTRef(this));
}

bool ArithLogic::isBuiltinFunction(const SymRef sr) const
{
    if (sym_store[sr].isInterpreted()) return true;
    else return Logic::isBuiltinFunction(sr);
}
bool ArithLogic::isNumTerm(PTRef tr) const
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

PTRef ArithLogic::mkNumAbs(PTRef tr) {
    checkArithSortCompatibleAndDefined(tr);
    if (isConstant(tr)) {
        return getNumConst(tr) >= 0 ? tr : mkNumNeg(tr);
    }
    if (isNumNeg(tr)) {
        return mkNumAbs(getPterm(tr)[0]);
    }
    if (isNumTimes(tr)) {
        vec<PTRef> args;
        for (auto arg_tr : getPterm(tr)) {
            args.push(mkNumAbs(arg_tr));
        }
        return mkNumTimes(args);
    }
    return mkFun(get_sym_Num_ABS(), {tr});
}

PTRef ArithLogic::mkNumNeg(PTRef tr)
{
    assert(!isNumNeg(tr)); // MB: The invariant now is that there is no "Minus" node
    if (isConstant(tr)) {
        const opensmt::Number& v = getNumConst(tr);
        return mkConst(-v);
    }
    if (isNumPlus(tr)) {
        vec<PTRef> args;
        args.capacity(getPterm(tr).size());
        for (int i = 0; i < getPterm(tr).size(); ++i) {
            PTRef tr_arg = mkNumNeg(getPterm(tr)[i]);
            assert(tr_arg != PTRef_Undef);
            args.push(tr_arg);
        }
        PTRef tr_n = mkFun(get_sym_Num_PLUS(), std::move(args));
        return tr_n;
    }
    PTRef mo = this->getTerm_NumMinusOne();
    return mkNumTimes(vec<PTRef>{mo, tr});
}

PTRef ArithLogic::mkConst(const opensmt::Number& c)
{
    checkArithSortDefined();
    std::string str = c.get_str(); // MB: I cannot store c.get_str().c_str() directly, since that is a pointer inside temporary object -> crash.
    const char * val = str.c_str();
    PTRef ptr = PTRef_Undef;
    ptr = mkVar(getSort_num(), val);
    // Store the value of the number as a real
    SymId id = sym_store[getPterm(ptr).symb()].getId();
    for (int i = numbers.size(); static_cast<unsigned int>(i) <= id; i++) { numbers.emplace_back(); }
    if (numbers[id] == nullptr) { numbers[id] = new opensmt::Number(val); }
    assert(c == *numbers[id]);
    markConstant(id);
    return ptr;
}

char* ArithLogic::printTerm(PTRef tr) const { return printTerm_(tr, false, false); }
char* ArithLogic::printTerm(PTRef tr, bool l, bool s) const { return printTerm_(tr, l, s); }

PTRef ArithLogic::mkNumMinus(vec<PTRef> && args)
{
    checkArithSortCompatible(args);
    assert(args.size() > 0);
    if (args.size() == 1) {
        return mkNumNeg(args[0]);
    }
    assert(args.size() == 2);
    if (args.size() > 2) { throw OsmtApiException("Too many terms provided to LALogic::mkNumMinus"); }

    PTRef mo = isIntegralLogic() ? term_Int_MINUSONE : term_Real_MINUSONE;

    PTRef fact = mkNumTimes(mo, args[1]);
    assert(fact != PTRef_Undef);
    args[1] = fact;
    return mkNumPlus(std::move(args));
}

PTRef ArithLogic::mkNumPlus(vec<PTRef> && args)
{
    checkArithSortCompatible(args);
    vec<PTRef> flattened_args;
    flattened_args.capacity(args.size());

    // Flatten possible internal sums.  This needs not be done properly,
    // with a post-order dfs, since we are guaranteed that the inner
    // sums are already flattened.
    for (auto tr : args) {
        if (isNumPlus(tr)) {
            Pterm const & t = getPterm(tr);
            for (auto j : t) {
                flattened_args.push(j);
            }
        } else {
            flattened_args.push(tr);
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

PTRef ArithLogic::mkNumTimes(vec<PTRef> && args)
{
    checkArithSortCompatible(args);
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
PTRef ArithLogic::mkBinaryLeq(PTRef lhs, PTRef rhs) {
    checkArithSortCompatibleAndDefined({lhs, rhs});
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

PTRef ArithLogic::mkBinaryGeq(PTRef lhs, PTRef rhs) {
    return mkBinaryLeq(rhs, lhs);
}

PTRef ArithLogic::mkBinaryLt(PTRef lhs, PTRef rhs) {
    return mkNot(mkBinaryGeq(lhs, rhs));
}

PTRef ArithLogic::mkBinaryGt(PTRef lhs, PTRef rhs) {
    return mkNot(mkBinaryLeq(lhs, rhs));
}

PTRef ArithLogic::mkNumLeq(vec<PTRef> const & args) {
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

PTRef ArithLogic::mkNumGeq(vec<PTRef> const & args) {
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

PTRef ArithLogic::mkNumLt(vec<PTRef> const & args)
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

PTRef ArithLogic::mkNumGt(vec<PTRef> const & args)
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

PTRef ArithLogic::mkBinaryEq(PTRef lhs, PTRef rhs) {
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

PTRef ArithLogic::mkIntMod(vec<PTRef> && args) {
    if (args.size() != 2) { throw OsmtApiException("Modulo needs exactly two arguments"); }
    PTRef dividend = args[0];
    PTRef divisor = args[1];
    checkSortInt(dividend);
    checkSortInt(divisor);


    if (not isNumConst(divisor)) { throw OsmtApiException("Divisor must be constant in linear logic"); }
    if (isNumZero(divisor)) { throw ArithDivisionByZeroException(); }

    if (isConstant(dividend)) {
        auto const& dividendValue = getNumConst(dividend);
        auto const& divisorValue = getNumConst(divisor);
        assert(dividendValue.isInteger() and divisorValue.isInteger());
        // evaluate immediately the operation on two constants
        auto realDiv = dividendValue / divisorValue;
        auto intDiv = divisorValue.sign() > 0 ? realDiv.floor() : realDiv.ceil();
        auto intMod = dividendValue - intDiv * divisorValue;
        assert(intMod.sign() >= 0 and intMod < abs(divisorValue));
        return mkConst(intMod);
    }
    return mkFun(sym_Int_MOD, {dividend, divisor});
}

PTRef ArithLogic::mkIntDiv(vec<PTRef> && args) {
    checkSortInt(args);
    assert(args.size() == 2);
    PTRef dividend = args[0];
    PTRef divisor = args[1];
    if (not isConstant(divisor) and not isConstant(dividend)) { throw LANonLinearException("Divisor or dividend must be constant in linear logic"); }
    if (isNumZero(divisor)) { throw ArithDivisionByZeroException(); }

    if (isConstant(divisor) and isConstant(dividend)) {
        auto const& dividendValue = getNumConst(dividend);
        auto const& divisorValue = getNumConst(divisor);
        assert(dividendValue.isInteger() and divisorValue.isInteger());
        // evaluate immediately the operation on two constants
        auto realDiv = dividendValue / divisorValue;
        auto intDiv = divisorValue.sign() > 0 ? realDiv.floor() : realDiv.ceil();
        return mkConst(intDiv);
    }
    return mkFun(sym_Int_DIV, std::move(args));
}

PTRef ArithLogic::mkRealDiv(vec<PTRef> && args)
{
    checkSortReal(args);
    if (args.size() != 2) {
        throw OsmtApiException("Division operation requires exactly 2 arguments");
    }
    if (this->isNumZero(args[1])) {
        throw ArithDivisionByZeroException();
    }
    if (not isConstant(args[1])) {
        throw LANonLinearException("Only division by constant is permitted in linear arithmetic!");
    }
    SimplifyConstDiv simp(*this);
    vec<PTRef> args_new;
    SymRef s_new;
    simp.simplify(get_sym_Real_DIV(), args, s_new, args_new);
    if (isRealDiv(s_new)) {
        assert((isNumTerm(args_new[0]) || isNumPlus(args_new[0])) && isConstant(args_new[1]));
        args_new[1] = mkConst(FastRational_inverse(getNumConst(args_new[1]))); //mkConst(1/getRealConst(args_new[1]));
        return mkNumTimes(args_new);
    }
    PTRef tr = mkFun(s_new, std::move(args_new));
    return tr;
}

PTRef ArithLogic::insertTerm(SymRef sym, vec<PTRef>&& terms)
{
    if (sym == sym_Int_NEG)
        return mkIntNeg(terms[0]);
    if (sym == sym_Real_NEG)
        return mkRealNeg(terms[0]);
    if (sym == sym_Int_MINUS)
        return mkIntMinus(std::move(terms));
    if (sym == sym_Real_MINUS)
        return mkRealMinus(std::move(terms));
    if (sym == sym_Int_PLUS)
        return mkIntPlus(std::move(terms));
    if (sym == sym_Real_PLUS)
        return mkRealPlus(std::move(terms));
    if (sym == sym_Int_TIMES)
        return mkIntTimes(std::move(terms));
    if (sym == sym_Real_TIMES)
        return mkRealTimes(std::move(terms));
    if (sym == sym_Real_DIV)
        return mkRealDiv(std::move(terms));
    if (sym == sym_Int_LEQ)
        return mkIntLeq(std::move(terms));
    if (sym == sym_Real_LEQ)
        return mkRealLeq(std::move(terms));
    if (sym == sym_Int_LT)
        return mkIntLt(std::move(terms));
    if (sym == sym_Real_LT)
        return mkRealLt(std::move(terms));
    if (sym == sym_Int_GEQ)
        return mkIntGeq(std::move(terms));
    if (sym == sym_Real_GEQ)
        return mkRealGeq(std::move(terms));
    if (sym == sym_Int_GT)
        return mkIntGt(std::move(terms));
    if (sym == sym_Real_GT)
        return mkRealGt(std::move(terms));
    if (extendedSignatureEnabled()) {
        if (sym == get_sym_Int_MOD())
            return mkIntMod(terms[0], terms[1]);
        if (sym == get_sym_Int_DIV())
            return mkIntDiv(std::move(terms));
        if (sym == sym_Int_ABS)
            return mkIntAbs(terms[0]);
    }
    if (sym == sym_Int_ITE or sym == sym_Real_ITE)
        return mkIte(std::move(terms));
    return Logic::insertTerm(sym, std::move(terms));
}

PTRef ArithLogic::mkConst(SRef s, const char* name)
{
    assert(strlen(name) != 0);
    PTRef ptr = PTRef_Undef;
    if (s == sort_REAL or s == sort_INT) {
        char* rat;
        if (s == sort_REAL)
            opensmt::stringToRational(rat, name);
        else {
            if (not opensmt::isIntString(name))
                throw OsmtApiException("Not parseable as an integer");
            rat = strdup(name);
        }
        ptr = mkVar(s, rat);
        // Store the value of the number as a real
        SymId id = sym_store[getPterm(ptr).symb()].getId();
        for (int i = numbers.size(); static_cast<unsigned>(i) <= id; i++)
            numbers.emplace_back(nullptr);
        if (numbers[id] != nullptr) { delete numbers[id]; }
        numbers[id] = new FastRational(rat);
        free(rat);
        markConstant(id);
    } else
        ptr = Logic::mkConst(s, name);
    return ptr;
}

/**
 * SMT-LIB style resolution of numeric constants.
 * @param name string representation of the constant
 * @return a PTRef of the correct sort representing the constant.
 */
PTRef ArithLogic::mkConst(char const * name) {
    bool isIntegralForm = opensmt::isIntString(name);
    bool isRealForm = opensmt::isRealString(name);

    if (isIntegralLogic()) {
        if (isRealForm and not isIntegralForm) {
            throw OsmtApiException("Expected integral constant");
        } else if (isIntegralForm) {
            return mkConst(sort_INT, name);
        }
    } else if (isRealLogic()) {
        if (isIntegralForm or isRealForm) {
            return mkConst(sort_REAL, name);
        }
    } else {
        // Logic has mixed arithmetic
        if (isIntegralForm) {
            return mkConst(sort_INT, name);
        } else if (isRealForm) {
            return mkConst(sort_REAL, name);
        }
    }
    // Not a numeric constant, so let Logic decide.
    return Logic::mkConst(name);
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
    for (auto tr : terms)
        if (not l.isNumZero(tr))
            terms_new.push(tr);
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
    for (auto tr : terms) {
        if (l.isNumZero(tr)) {
            terms_new.clear();
            s_new = l.getPterm(l.getTerm_NumZero()).symb();
            return;
        }
        if ( not l.isNumOne(tr)) {
            if (l.isNumPlus(tr)) {
                plus = tr;
            } else if (l.isConstant(tr)) {
                con = tr;
            } else {
                terms_new.push(tr);
            }
        }
    }
    if (con == PTRef_Undef and plus == PTRef_Undef);
    else if (con == PTRef_Undef and plus != PTRef_Undef)
        terms_new.push(plus);
    else if (con != PTRef_Undef and plus == PTRef_Undef)
        terms_new.push(con);
    else {
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

const char*
ArithLogic::getDefaultValue(const PTRef tr) const
{
    if (getSortRef(tr) == sort_INT)
        return tk_val_int_default.data();
    else if (getSortRef(tr) == sort_REAL)
        return tk_val_real_default.data();
    else
        return Logic::getDefaultValue(tr);
}

PTRef
ArithLogic::getDefaultValuePTRef(const SRef sref) const
{
    if (sref == getSort_num())
        return getTerm_NumZero();
    else
        return Logic::getDefaultValuePTRef(sref);
}


// Handle the printing of real constants that are negative and the
// rational constants
char*
ArithLogic::printTerm_(PTRef tr, bool ext, bool safe) const
{
    char* out;
    if (isNumConst(tr)) {
        bool is_neg = false;
        char* tmp_str;
        opensmt::stringToRational(tmp_str, sym_store.getName(getPterm(tr).symb()));
        opensmt::Number v(tmp_str);
        if (!isNonnegNumConst(tr)) {
            v = -v;
            is_neg = true;
        }
        char* rat_str = strdup(v.get_str().c_str());
        free(tmp_str);
        bool is_div = false;
        int i = 0;
        for (; rat_str[i] != '\0'; i++) {
            if (rat_str[i] == '/') {
                is_div = true;
                break;
            }
        }
        if (is_div) {
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
            } else {
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
        } else
            out = rat_str;
    }
    else
        out = Logic::printTerm_(tr, ext, safe);
    return out;
}

/**
 * Normalizes a sum term a1x1 + a2xn + ... + anxn + c such that the coefficients of non-constant terms are coprime integers
 * Additionally, the normalized term is separated to constant and non-constant part, and the constant is modified as if
 * it was placed on the other side of an equality.
 * Note that the constant part can be a non-integer number after normalization.
 *
 * @param sum
 * @return Constant part of the normalized sum as LHS and non-constant part of the normalized sum as RHS
 */
opensmt::pair<FastRational, PTRef> ArithLogic::sumToNormalizedIntPair(PTRef sum) {

    auto [constantValue, varFactors] = getConstantAndFactors(sum);

    vec<PTRef> vars; vars.capacity(varFactors.size());
    std::vector<opensmt::Number> coeffs; coeffs.reserve(varFactors.size());
    for (PTRef factor : varFactors) {
        PTRef var;
        PTRef coeff;
        splitTermToVarAndConst(factor, var, coeff);
        assert(ArithLogic::isNumVarLike(var) and isNumConst(coeff));
        vars.push(var);
        coeffs.push_back(getNumConst(coeff));
    }
    bool changed = false; // Keep track if any change to varFactors occurs

    bool allIntegers = std::all_of(coeffs.begin(), coeffs.end(),
                                   [](opensmt::Number const & coeff) { return coeff.isInteger(); });
    if (not allIntegers) {
        // first ensure that all coeffs are integers
        using Integer = FastRational; // TODO: change when we have FastInteger
        auto lcmOfDenominators = Integer(1);
        auto accumulateLCMofDenominators = [&lcmOfDenominators](FastRational const & next) {
            if (next.isInteger()) {
                // denominator is 1 => lcm of denominators stays the same
                return;
            }
            Integer den = next.get_den();
            if (lcmOfDenominators == 1) {
                lcmOfDenominators = std::move(den);
                return;
            }
            lcmOfDenominators = lcm(lcmOfDenominators, den);
        };
        std::for_each(coeffs.begin(), coeffs.end(), accumulateLCMofDenominators);
        for (auto & coeff : coeffs) {
            coeff *= lcmOfDenominators;
            assert(coeff.isInteger());
        }
        // DONT forget to update also the constant factor
        constantValue *= lcmOfDenominators;
        changed = true;
    }
    assert(std::all_of(coeffs.begin(), coeffs.end(), [](opensmt::Number const & coeff) { return coeff.isInteger(); }));
    // Now make sure all coeffs are coprime
    auto coeffs_gcd = abs(coeffs[0]);
    for (std::size_t i = 1; i < coeffs.size() && coeffs_gcd != 1; ++i) {
        coeffs_gcd = gcd(coeffs_gcd, abs(coeffs[i]));
        assert(coeffs_gcd.isInteger());
    }
    if (coeffs_gcd != 1) {
        for (auto & coeff : coeffs) {
            coeff /= coeffs_gcd;
            assert(coeff.isInteger());
        }
        // DONT forget to update also the constant factor
        constantValue /= coeffs_gcd;
        changed = true;
    }
    // update the factors
    if (changed) {
        for (int i = 0; i < varFactors.size(); ++i) {
            varFactors[i] = mkIntTimes(vars[i], mkConst(coeffs[i]));
        }
    }
    PTRef normalizedSum = varFactors.size() == 1 ? varFactors[0] : mkFun(get_sym_Int_PLUS(), std::move(varFactors));
    // 0 <= normalizedSum + constatValue
    constantValue.negate();
    return {std::move(constantValue), normalizedSum};
}

/**
 * Normalizes a sum term a1x1 + a2xn + ... + anxn + c such that the leading coefficient is either 1 or -1.
 * Additionally, the normalized term is separated to constant and non-constant part, and the constant is modified as if
 * it was placed on the other side of an equality.
 *
 * @param sum
 * @return Constant part of the normalized sum as LHS and non-constant part of the normalized sum as RHS
 */

opensmt::pair<opensmt::Number, PTRef> ArithLogic::sumToNormalizedRealPair(PTRef sum) {

    auto [constantValue, varFactors] = getConstantAndFactors(sum);

    PTRef leadingFactor = varFactors[0];
    // normalize the sum according to the leading factor
    PTRef var, coeff;
    splitTermToVarAndConst(leadingFactor, var, coeff);
    opensmt::Number normalizationCoeff = abs(getNumConst(coeff));
    // varFactors come from a normalized sum, no need to call normalization code again
    PTRef normalizedSum = varFactors.size() == 1 ? varFactors[0] : mkFun(get_sym_Real_PLUS(), std::move(varFactors));
    if (normalizationCoeff != 1) {
        // normalize the whole sum
        normalizedSum = mkNumTimes(normalizedSum, mkConst(normalizationCoeff.inverse()));
        // DON'T forget to update also the constant factor!
        constantValue /= normalizationCoeff;
    }
    constantValue.negate(); // moving the constant to the LHS of the inequality
    return {std::move(constantValue), normalizedSum};
}

opensmt::pair<FastRational, PTRef> ArithLogic::sumToNormalizedPair(PTRef sum) {
    if (isIntegralLogic()) {
        return sumToNormalizedIntPair(sum);
    } else if (isRealLogic()) {
        return sumToNormalizedRealPair(sum);
    } else {
        throw OsmtApiException("Numeric sort is ambiguous");
    }
}

PTRef ArithLogic::intSumToNormalizedInequality(PTRef sum) {
    auto [lhsVal, rhs] = sumToNormalizedPair(sum);
    return mkFun(get_sym_Int_LEQ(), {mkConst(lhsVal.ceil()), rhs});
}

PTRef ArithLogic::intSumToNormalizedEquality(PTRef sum) {
    auto [lhsVal, rhs] = sumToNormalizedPair(sum);
    if (not lhsVal.isInteger()) { return getTerm_false(); }
    return mkFun(get_sym_Int_EQ(), {mkConst(lhsVal), rhs});
}

PTRef ArithLogic::realSumToNormalizedInequality(PTRef sum) {
    auto [lhsVal, rhs] = sumToNormalizedPair(sum);
    return mkFun(get_sym_Real_LEQ(), {mkConst(lhsVal), rhs});
}

PTRef ArithLogic::realSumToNormalizedEquality(PTRef sum) {
    auto [lhsVal, rhs] = sumToNormalizedPair(sum);
    return mkFun(get_sym_Real_EQ(), {mkConst(lhsVal), rhs});
}

PTRef ArithLogic::sumToNormalizedInequality(PTRef sum) {
    if (not isIntegralLogic() and not isRealLogic()) {
        throw OsmtInternalException("Normalization of mixed inequalities not supported yet. ");
    }
    return isIntegralLogic() ? intSumToNormalizedInequality(sum) : realSumToNormalizedInequality(sum);
}

PTRef ArithLogic::sumToNormalizedEquality(PTRef sum) {
    if (not isIntegralLogic() and not isRealLogic()) {
        throw OsmtInternalException("Normalization of mixed inequalities not supported yet. ");
    }
    return isIntegralLogic() ? intSumToNormalizedEquality(sum) : realSumToNormalizedEquality(sum);
}

PTRef ArithLogic::getConstantFromLeq(PTRef leq) {
    Pterm const & term = getPterm(leq);
    if (not isNumLeq(term.symb())) {
        throw OsmtApiException("LALogic::getConstantFromLeq called on a term that is not less-or-equal inequality");
    }
    return term[0];
}

PTRef ArithLogic::getTermFromLeq(PTRef leq) {
    Pterm const & term = getPterm(leq);
    if (not isNumLeq(term.symb())) {
        throw OsmtApiException("LALogic::getConstantFromLeq called on a term that is not less-or-equal inequality");
    }
    return term[1];
}

std::pair<PTRef, PTRef> ArithLogic::leqToConstantAndTerm(PTRef leq) {
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


