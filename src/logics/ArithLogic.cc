#include "SStore.h"
#include "PtStore.h"
#include "TreeOps.h"
#include "StringConv.h"
#include "LA.h"
#include "ArithLogic.h"
#include "FastRational.h"
#include "OsmtInternalException.h"
#include "OsmtApiException.h"
#include "IteHandler.h"
#include "DivModRewriter.h"
#include "Polynomial.h"
#include <memory>
#include <sstream>
const std::string ArithLogic::e_nonlinear_term = "Logic does not support nonlinear terms";

/***********************************************************
 * Class defining simplifications
 ***********************************************************/

namespace{
class SimplifyConst {
protected:
    ArithLogic& l;
    virtual void Op(opensmt::Number& s, const opensmt::Number& v) const = 0;
    virtual opensmt::Number getIdOp() const = 0;
    virtual void constSimplify(SymRef s, vec<PTRef> const & terms, SymRef & s_new, vec<PTRef> & terms_new) const = 0;
public:
    SimplifyConst(ArithLogic& log) : l(log) {}
    void simplify(SymRef s, vec<PTRef> const & terms, SymRef & s_new, vec<PTRef> & terms_new);
    PTRef simplifyConstOp(const vec<PTRef> & const_terms);
};

class SimplifyConstSum : public SimplifyConst {
    void Op(opensmt::Number& s, const opensmt::Number& v) const { s += v; }
    opensmt::Number getIdOp() const { return 0; }
    void constSimplify(SymRef s, vec<PTRef> const & terms, SymRef & s_new, vec<PTRef> & terms_new) const;
public:
    SimplifyConstSum(ArithLogic& log) : SimplifyConst(log) {}
};

class SimplifyConstTimes : public SimplifyConst {
    void Op(opensmt::Number& s, const opensmt::Number& v) const { s *= v; }
    opensmt::Number getIdOp() const { return 1; }
    void constSimplify(SymRef s, vec<PTRef> const & terms, SymRef & s_new, vec<PTRef> & terms_new) const;
public:
    SimplifyConstTimes(ArithLogic& log) : SimplifyConst(log) {}
};

class SimplifyConstDiv : public SimplifyConst {
    void Op(opensmt::Number& s, const opensmt::Number& v) const { if (v == 0) { printf("explicit div by zero\n"); } s /= v; }
    opensmt::Number getIdOp() const { return 1; }
    void constSimplify(SymRef s, vec<PTRef> const & terms, SymRef & s_new, vec<PTRef> & terms_new) const;
public:
    SimplifyConstDiv(ArithLogic& log) : SimplifyConst(log) {}
};
}

const std::string ArithLogic::tk_int_zero  = "0";
const std::string ArithLogic::tk_int_one   = "1";
const std::string ArithLogic::tk_int_neg   = "-";
const std::string ArithLogic::tk_int_minus = "-";
const std::string ArithLogic::tk_int_plus  = "+";
const std::string ArithLogic::tk_int_times = "*";
const std::string ArithLogic::tk_int_div   = "div";
const std::string ArithLogic::tk_int_mod   = "mod";
const std::string ArithLogic::tk_int_lt    = "<";
const std::string ArithLogic::tk_int_leq   = "<=";
const std::string ArithLogic::tk_int_gt    = ">";
const std::string ArithLogic::tk_int_geq   = ">=";

const std::string ArithLogic::s_sort_int = "Int";

const std::string ArithLogic::tk_real_zero  = "0.0";
const std::string ArithLogic::tk_real_one   = "1.0";
const std::string ArithLogic::tk_real_neg   = "-";
const std::string ArithLogic::tk_real_minus = "-";
const std::string ArithLogic::tk_real_plus  = "+";
const std::string ArithLogic::tk_real_times = "*";
const std::string ArithLogic::tk_real_div   = "/";
const std::string ArithLogic::tk_real_lt    = "<";
const std::string ArithLogic::tk_real_leq   = "<=";
const std::string ArithLogic::tk_real_gt    = ">";
const std::string ArithLogic::tk_real_geq   = ">=";
const std::string ArithLogic::s_sort_real   = "Real";

const std::string ArithLogic::tk_val_int_default  = "0";
const std::string ArithLogic::tk_val_real_default = "0.0";

ArithLogic::ArithLogic(opensmt::Logic_t type)
    : Logic(type)

    , sort_REAL(getSort(sort_store.newSortSymbol(SortSymbol(s_sort_real, 0, SortSymbol::INTERNAL)), {}))
    , term_Real_ZERO(mkConst(sort_REAL, tk_real_zero.c_str()))
    , term_Real_ONE(mkConst(sort_REAL, tk_real_one.c_str()))
    , term_Real_MINUSONE(mkConst(sort_REAL, tk_real_minus + tk_real_one))
    , sym_Real_ZERO(getSymRef(term_Real_ZERO))
    , sym_Real_ONE(getSymRef(term_Real_ONE))
    , sym_Real_NEG(declareFun_NoScoping(tk_real_neg, sort_REAL, {sort_REAL}))
    , sym_Real_MINUS(declareFun_NoScoping_LeftAssoc(tk_real_minus, sort_REAL, {sort_REAL, sort_REAL}))
    , sym_Real_PLUS(declareFun_Commutative_NoScoping_LeftAssoc(tk_real_plus, sort_REAL, {sort_REAL, sort_REAL}))
    , sym_Real_TIMES(declareFun_Commutative_NoScoping_LeftAssoc(tk_real_times, sort_REAL, {sort_REAL, sort_REAL}))
    , sym_Real_DIV(declareFun_NoScoping_LeftAssoc(tk_real_div, sort_REAL, {sort_REAL, sort_REAL}))
    , sym_Real_EQ(sortToEquality[sort_REAL])
    , sym_Real_LEQ(declareFun_NoScoping_Chainable(tk_real_leq, sort_BOOL, {sort_REAL, sort_REAL}))
    , sym_Real_LT(declareFun_NoScoping_Chainable(tk_real_lt, sort_BOOL, {sort_REAL, sort_REAL}))
    , sym_Real_GEQ(declareFun_NoScoping_Chainable(tk_real_geq, sort_BOOL, {sort_REAL, sort_REAL}))
    , sym_Real_GT(declareFun_NoScoping_Chainable(tk_real_gt, sort_BOOL, {sort_REAL, sort_REAL}))
    , sym_Real_ITE(sortToIte[sort_REAL])
    , sym_Real_DISTINCT(sortToDisequality[sort_REAL])

    , sort_INT(getSort(sort_store.newSortSymbol(SortSymbol(s_sort_int, 0, SortSymbol::INTERNAL)), {}))
    , term_Int_ZERO(mkConst(sort_INT, tk_int_zero))
    , term_Int_ONE(mkConst(sort_INT, tk_int_one.c_str()))
    , term_Int_MINUSONE(mkConst(sort_INT, tk_int_minus + tk_int_one))
    , sym_Int_ZERO(getSymRef(term_Int_ZERO))
    , sym_Int_ONE(getSymRef(term_Int_ONE))
    , sym_Int_NEG(declareFun_NoScoping(tk_int_neg, sort_INT, {sort_INT}))
    , sym_Int_MINUS(declareFun_NoScoping_LeftAssoc(tk_int_minus, sort_INT, {sort_INT, sort_INT}))
    , sym_Int_PLUS(declareFun_Commutative_NoScoping_LeftAssoc(tk_int_plus, sort_INT, {sort_INT, sort_INT}))
    , sym_Int_TIMES(declareFun_Commutative_NoScoping_LeftAssoc(tk_int_times, sort_INT, {sort_INT, sort_INT}))
    , sym_Int_DIV(declareFun_NoScoping_LeftAssoc(tk_int_div, sort_INT, {sort_INT, sort_INT}))
    , sym_Int_MOD(declareFun_NoScoping(tk_int_mod, sort_INT, {sort_INT, sort_INT}))
    , sym_Int_EQ(sortToEquality[sort_INT])
    , sym_Int_LEQ(declareFun_NoScoping_Chainable(tk_int_leq, sort_BOOL, {sort_INT, sort_INT}))
    , sym_Int_LT(declareFun_NoScoping_Chainable(tk_int_lt, sort_BOOL, {sort_INT, sort_INT}))
    , sym_Int_GEQ(declareFun_NoScoping_Chainable(tk_int_geq, sort_BOOL, {sort_INT, sort_INT}))
    , sym_Int_GT(declareFun_NoScoping_Chainable(tk_int_gt, sort_BOOL, {sort_INT, sort_INT}))
    , sym_Int_ITE(sortToIte[sort_INT])
    , sym_Int_DISTINCT(sortToDisequality[sort_INT])
{ }

SymRef ArithLogic::getPlusForSort(SRef sort) const {
    assert (sort == getSort_int() or sort == getSort_real());
    return sort == getSort_int() ? get_sym_Int_PLUS() : get_sym_Real_PLUS();
}

SymRef ArithLogic::getTimesForSort(SRef sort) const {
    assert (sort == getSort_int() or sort == getSort_real());
    return sort == getSort_int() ? get_sym_Int_TIMES() : get_sym_Real_TIMES();
}

SymRef ArithLogic::getMinusForSort(SRef sort) const {
    assert (sort == getSort_int() or sort == getSort_real());
    return sort == getSort_int() ? get_sym_Int_MINUS() : get_sym_Real_MINUS();
};

PTRef ArithLogic::getZeroForSort(SRef sort) const {
    assert (sort == getSort_int() or sort == getSort_real());
    return sort == getSort_int() ? getTerm_IntZero() : getTerm_RealZero();
}

PTRef ArithLogic::getOneForSort(SRef sort) const {
    assert (sort == getSort_int() or sort == getSort_real());
    return sort == getSort_int() ? getTerm_IntOne() : getTerm_RealOne();
}

PTRef ArithLogic::getMinusOneForSort(SRef sort) const {
    assert (sort == getSort_int() or sort == getSort_real());
    return sort == getSort_int() ? getTerm_IntMinusOne() : getTerm_RealMinusOne();
}

bool ArithLogic::isLinearFactor(PTRef tr) const {
    if (isNumConst(tr) || isNumVarLike(tr)) { return true; }
    if (isTimes(tr)) {
        Pterm const& term = getPterm(tr);
        return term.size() == 2 && ((isNumConst(term[0]) && (isNumVarLike(term[1])))
                                    || (isNumConst(term[1]) && (isNumVarLike(term[0]))));
    }
    return false;
}

bool ArithLogic::isLinearTerm(PTRef tr) const {
    if (isLinearFactor(tr)) { return true; }
    if (isPlus(tr)) {
        Pterm const& term = getPterm(tr);
        return std::all_of(term.begin(), term.end(), [this](PTRef tr) { return isLinearFactor(tr); });
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

opensmt::pair<opensmt::Number, vec<PTRef>> ArithLogic::getConstantAndFactors(PTRef sum) const {
    assert(isPlus(sum));
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
    if (constant == PTRef_Undef) { constant = isIntPlus(sum) ? getTerm_IntZero() : getTerm_RealZero(); }
    auto constantValue = getNumConst(constant);
    assert(varFactors.size() > 0);
    termSort(varFactors);
    return {std::move(constantValue), std::move(varFactors)};
}

opensmt::pair<PTRef, PTRef> ArithLogic::splitTermToVarAndConst(PTRef term) const
{
    assert(isTimes(term) || isNumVarLike(term) || isConstant(term));
    if (isTimes(term)) {
        assert(getPterm(term).size() == 2);
        PTRef fac = getPterm(term)[0];
        PTRef var = getPterm(term)[1];
        if (not isConstant(fac)) {
            std::swap(fac, var);
        }
        assert(isConstant(fac));
        assert(isNumVarLike(var));
        return {var, fac};
    } else if (isNumVarLike(term)) {
        assert(yieldsSortInt(term) or yieldsSortReal(term));
        PTRef var = term;
        PTRef fac = yieldsSortInt(term) ? getTerm_IntOne() : getTerm_RealOne();
        return {var, fac};
    } else {
        assert(isConstant(term));
        return {PTRef_Undef, term};
    }
}

// Normalize a product of the form (* a v) to either v or (* -1 v)
PTRef ArithLogic::normalizeMul(PTRef mul)
{
    assert(isTimes(mul));
    auto [v,c] = splitTermToVarAndConst(mul);
    if (getNumConst(c) < 0) {
        return mkNeg(v);
    } else {
        return v;
    }
}

namespace{
using poly_t = PolynomialT<PTRef>;
Logic::SubstMap collectConstantSubstitutions(ArithLogic & logic, std::vector<poly_t> & zeroPolynomials) {
    Logic::SubstMap substitutions;

    while (true) {
        vec<PTRef> new_keys;
        std::vector<std::size_t> processedIndices;
        std::unordered_map<PTRef, std::vector<std::size_t>, PTRefHash> varToPolyIndices;

        for (std::size_t i = 0; i < zeroPolynomials.size(); ++i) {
            auto const & poly = zeroPolynomials[i];
            assert(poly.size() > 0);
            for (auto const & term : poly) {
                varToPolyIndices[term.var].push_back(i);
            }

            if (poly.size() == 1) {
                auto const & term = *poly.begin();
                if (term.var == PTRef_Undef) { // FALSE equality
                    continue;
                }
                // poly is "x = 0"
                PTRef var = term.var;
                if (not substitutions.has(var)) {
                    substitutions.insert(var, logic.getZeroForSort(logic.getSortRef(var)));
                    new_keys.push(var);
                }
                processedIndices.push_back(i);
                varToPolyIndices.at(var).pop_back();
                continue;
            }
            assert(poly.begin()->var != PTRef_Undef);
            if (poly.size() == 2 and (poly.begin() + 1)->var == PTRef_Undef) { // poly is "a*x + c = 0" for c != 0
                auto const & term = *poly.begin();
                PTRef var = term.var;
                if (not substitutions.has(var)) {
                    auto val = -((poly.begin() + 1)->coeff) / term.coeff;
                    substitutions.insert(var, logic.mkConst(logic.getSortRef(var), val));
                    new_keys.push(var);
                }
                processedIndices.push_back(i);
                varToPolyIndices.at(var).pop_back();
                continue;
            }
        }

        // Apply found substitutions
        bool changed = false;
        for (PTRef var : new_keys) {
            for (std::size_t index : varToPolyIndices.at(var)) {
                auto & poly = zeroPolynomials[index];
                auto coeff = poly.removeVar(var);
                auto val = substitutions[var];
                if (not logic.isZero(val)) {
                    poly_t constantPoly;
                    constantPoly.addTerm(PTRef_Undef, coeff * logic.getNumConst(val));
                    poly.merge(constantPoly, 1);
                }
                changed = true;
            }
        }
        // remove used polynomials
        auto lastValid = zeroPolynomials.size() - 1;
        for (auto rit = processedIndices.rbegin(); rit != processedIndices.rend(); ++rit) {
            auto index = *rit;
            zeroPolynomials[index] = std::move(zeroPolynomials[lastValid]);
            zeroPolynomials.pop_back();
            --lastValid;
        }

        if (not changed) { break; }
    }
    return substitutions;
}

PTRef polyToPTRef(ArithLogic & logic, poly_t poly) {
    vec<PTRef> args;
    args.capacity(poly.size());
    assert(poly.size() > 0);
    assert(poly.begin()->var != PTRef_Undef);
    SRef sortRef = logic.getSortRef(poly.begin()->var);
    for (auto const & term : poly) {
        assert(not term.coeff.isZero());
        if (term.var == PTRef_Undef) { args.push(logic.mkConst(sortRef, term.coeff)); }
        else if (term.coeff.isOne()) { args.push(term.var); }
        else { args.push(logic.mkTimes(term.var, logic.mkConst(logic.getSortRef(term.var), term.coeff))); }
    }
    return logic.mkPlus(std::move(args)); // TODO: Can we use non-simplifying versions of mkPlus/mkTimes?
}

Logic::SubstMap collectSingleEqualitySubstitutions(ArithLogic & logic, std::vector<poly_t> & zeroPolynomials) {
    Logic::SubstMap substitutions;
    std::unordered_map<PTRef, std::vector<std::size_t>, PTRefHash> varToPolyIndices;

    for (std::size_t i = 0; i < zeroPolynomials.size(); ++i) {
        auto const & poly = zeroPolynomials[i];
        for (auto const & term : poly) {
            varToPolyIndices[term.var].push_back(i);
        }
    }

    std::unordered_set<std::size_t> processedIndices;
    for (auto const & entry : varToPolyIndices) {
        if (entry.second.size() != 1 or entry.first == PTRef_Undef) { continue; }
        auto index = entry.second[0];
        PTRef var = entry.first;
        auto [it, inserted] = processedIndices.insert(index);
        if (not inserted) { continue; }
        auto & poly = zeroPolynomials[index];
        auto coeff = poly.removeVar(var);
        coeff.negate();
        if (not coeff.isOne()) {
            poly.divideBy(coeff);
        }
        PTRef val = polyToPTRef(logic, poly);
        substitutions.insert(var, val);
    }
    // Remove processed polynomials
    std::vector<std::size_t> indicesToRemove(processedIndices.begin(), processedIndices.end());
    std::sort(indicesToRemove.begin(), indicesToRemove.end());
    auto lastValid = zeroPolynomials.size() - 1;
    for (auto rit = indicesToRemove.rbegin(); rit != indicesToRemove.rend(); ++rit) {
        auto index = *rit;
        zeroPolynomials[index] = std::move(zeroPolynomials[lastValid]);
        zeroPolynomials.pop_back();
        --lastValid;
    }
    return substitutions;
}
}

lbool ArithLogic::arithmeticElimination(const vec<PTRef> & top_level_arith, SubstMap & out_substitutions)
{
    ArithLogic & logic = *this;
    auto toPoly = [&logic](PTRef eq) {
        assert(logic.isEquality(eq));
        poly_t poly;
        PTRef polyTerm = logic.mkMinus(logic.getPterm(eq)[0], logic.getPterm(eq)[1]);
        assert(logic.isLinearTerm(polyTerm));
        if (logic.isLinearFactor(polyTerm)) {
            auto [var,c] = logic.splitTermToVarAndConst(polyTerm);
            auto coeff = logic.getNumConst(c);
            poly.addTerm(var, std::move(coeff));
        } else {
            for (PTRef factor : logic.getPterm(polyTerm)) {
                auto [var,c] = logic.splitTermToVarAndConst(factor);
                auto coeff = logic.getNumConst(c);
                poly.addTerm(var, std::move(coeff));
            }
        }
        return poly;
    };
    std::vector<poly_t> polynomials;
    polynomials.reserve(top_level_arith.size_());
    std::transform(top_level_arith.begin(), top_level_arith.end(), std::back_inserter(polynomials), toPoly);

    auto constSubstitutions = collectConstantSubstitutions(logic, polynomials);
    for (PTRef key : constSubstitutions.getKeys()) {
        assert(not out_substitutions.has(key));
        out_substitutions.insert(key, constSubstitutions[key]);
    }

    auto singleEqSubstitutions = collectSingleEqualitySubstitutions(logic, polynomials);
    for (PTRef key : singleEqSubstitutions.getKeys()) {
        assert(not out_substitutions.has(key));
        out_substitutions.insert(key, singleEqSubstitutions[key]);
    }

    for (auto & poly : polynomials) {
        // solve polynomial with respect to its first variable
        assert(poly.size() > 0);
        PTRef var = poly.begin()->var;
        if (out_substitutions.has(var)) {
            // Already have a substitution for this variable; skip this equality, let the main loop deal with this
            continue;
        }
        assert(var != PTRef_Undef);
        auto coeff = poly.removeVar(var);
        coeff.negate();
        if (not coeff.isOne()) {
            poly.divideBy(coeff);
        }
        PTRef val = polyToPTRef(logic, poly);
        assert(not out_substitutions.has(var));
        out_substitutions.insert(var, val);
    }
    // To simplify this method, we do not try to detect a conflict here, so result is always l_Undef
    return l_Undef;
}

opensmt::pair<lbool,Logic::SubstMap> ArithLogic::retrieveSubstitutions(const vec<PtAsgn>& facts)
{
    auto resAndSubsts = Logic::retrieveSubstitutions(facts);
    if (resAndSubsts.first != l_Undef) return resAndSubsts;
    vec<PTRef> top_level_arith;
    for (PtAsgn fact : facts) {
        PTRef tr = fact.tr;
        lbool sgn = fact.sgn;
        if (isNumEq(tr) && sgn == l_True)
            top_level_arith.push(tr);
    }
    lbool res = arithmeticElimination(top_level_arith, resAndSubsts.second);
    return {res, std::move(resAndSubsts.second)};
}

uint32_t LessThan_deepPTRef::getVarIdFromProduct(PTRef tr) const {
    assert(l.isTimes(tr));
    auto [v,c] = l.splitTermToVarAndConst(tr);
    return v.x;
}

bool LessThan_deepPTRef::operator()(PTRef x_, PTRef y_) const {
    uint32_t id_x = l.isTimes(x_) ? getVarIdFromProduct(x_) : x_.x;
    uint32_t id_y = l.isTimes(y_) ? getVarIdFromProduct(y_) : y_.x;
    return id_x < id_y;
}

void ArithLogic::termSort(vec<PTRef>& v) const
{
    sort(v, LessThan_deepPTRef(*this));
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
    if (t.size() == 2 && isTimes(tr))
        return (isNumVarLike(t[0]) && isConstant(t[1])) || (isNumVarLike(t[1]) && isConstant(t[0]));
    else if (t.size() == 0)
        return isNumVar(tr) || isConstant(tr);
    else
        return false;
}

PTRef ArithLogic::mkNeg(PTRef tr)
{
    assert(!isNeg(tr)); // MB: The invariant now is that there is no "Minus" node
    SymRef symref = getSymRef(tr);
    if (isConstant(symref)) {
        const opensmt::Number& v = getNumConst(tr);
        return mkConst(getSortRef(tr), -v);
    }
    if (isPlus(symref)) {
        vec<PTRef> args;
        args.capacity(getPterm(tr).size());
        // Note: Do this in two phases to avoid calling mkNeg that invalidates the Pterm reference
        for (PTRef tr_arg : getPterm(tr)) {
            assert(tr_arg != PTRef_Undef);
            args.push(tr_arg);
        }
        for (PTRef & tr_arg: args) {
            tr_arg = mkNeg(tr_arg);
        }
        PTRef tr_n = mkFun(symref, std::move(args));
        return tr_n;
    }
    if (isTimes(symref)) { // constant * var-like
        assert(getPterm(tr).size() == 2);
        auto [var, constant] = splitTermToVarAndConst(tr);
        return constant == getMinusOneForSort(getSortRef(symref)) ? var : mkFun(symref, {var, mkNeg(constant)});
    }
    if (isNumVarLike(symref)) {
        auto sortRef = getSortRef(symref);
        return mkFun(getTimesForSort(sortRef), {tr, getMinusOneForSort(sortRef)});
    }
    // MB: All cases should be covered
    throw OsmtInternalException("Failed attempt to negate a term");
}

PTRef ArithLogic::mkConst(SRef sort, opensmt::Number const & c)
{
    std::string str = c.get_str(); // MB: I cannot store c.get_str().c_str() directly, since that is a pointer inside temporary object -> crash.
    const char * val = str.c_str();
    PTRef ptr = PTRef_Undef;
    ptr = mkVar(sort, val, true);
    // Store the value of the number as a real
    SymId id = sym_store[getPterm(ptr).symb()].getId();
    for (auto i = numbers.size(); i <= id; i++) { numbers.emplace_back(); }
    if (numbers[id] == nullptr) { numbers[id] = new opensmt::Number(val); }
    assert(c == *numbers[id]);
    markConstant(id);
    return ptr;
}

PTRef ArithLogic::mkMinus(vec<PTRef> && args)
{
    SRef sort = checkArithSortCompatible(args);
    assert(args.size() > 0);
    if (args.size() == 1) {
        return mkNeg(args[0]);
    }
    assert(args.size() == 2);
    if (args.size() > 2) { throw OsmtApiException("Too many terms provided to LALogic::mkNumMinus"); }

    PTRef mo = getMinusOneForSort(sort);

    PTRef fact = mkTimes(mo, args[1]);
    assert(fact != PTRef_Undef);
    args[1] = fact;
    return mkPlus(std::move(args));
}

PTRef ArithLogic::mkPlus(vec<PTRef> && args)
{
    SRef returnSort = checkArithSortCompatible(args);
    SymRef plusSym = getPlusForSort(returnSort);
    vec<PTRef> flattened_args;
    flattened_args.capacity(args.size());

    // Flatten possible internal sums.  This needs not be done properly,
    // with a post-order dfs, since we are guaranteed that the inner
    // sums are already flattened.
    for (auto tr : args) {
        if (isPlus(tr)) {
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
    simp.simplify(plusSym, flattened_args, s_new, args);
    if (s_new != getPlusForSort(returnSort)) {
        return mkFun(s_new, std::move(args));
    }
    if (args.size() == 1) {
        return args[0];
    }
    // This code takes polynomials (+ (* v c1) (* v c2)) and converts them to the form (* v c3) where c3 = c1+c2
    VecMap<PTRef,PTRef,PTRefHash> s2t;
    vec<PTRef> keys;
    for (PTRef arg : args) {
        auto [v,c] = splitTermToVarAndConst(arg);
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
        PTRef consts_summed = consts.size() == 1 ? consts[0] : SimplifyConstSum(*this).simplifyConstOp(consts);
        if (isZero(consts_summed)) { continue; }
        if (key == PTRef_Undef) {
            flattened_args.push(consts_summed);
            continue;
        }
        if (isOne(consts_summed)) {
            flattened_args.push(key);
            continue;
        }
        // default case, variable and constant (cannot be simplified)
        PTRef term = mkFun(getTimesForSort(returnSort), {consts_summed, key});
        flattened_args.push(term);
    }
    if (flattened_args.size() == 0) return getZeroForSort(returnSort);
    if (flattened_args.size() == 1) return flattened_args[0];
    PTRef tr = mkFun(s_new, std::move(flattened_args));
    return tr;
}

PTRef ArithLogic::mkTimes(vec<PTRef> && args) {
    SRef returnSort = checkArithSortCompatible(args);
    if (args.size() == 2) { // MB: Multiplication by -1 as negation is more efficient
        PTRef minusOne = getMinusOneForSort(returnSort);
       if (minusOne == args[0]) {
           return mkNeg(args[1]);
       } else if (minusOne == args[1]) {
           return mkNeg(args[0]);
       }
       // else continue the usual normalization
    }
    vec<PTRef> flatten_args;
    // Flatten possible internal multiplications
    for (PTRef arg : args) {
        if (isTimes(arg)) {
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
    simp.simplify(getTimesForSort(returnSort), flatten_args, s_new, args);
    PTRef tr = mkFun(s_new, std::move(args));
    // Either a real term or, if we constructed a multiplication of a
    // constant and a sum, a real sum.
    if (isNumTerm(tr) || isPlus(tr) || isUF(tr) || isIte(tr))
        return tr;
    else {
        auto termStr = pp(tr);
        throw LANonLinearException(termStr.c_str());
    }
}

SymRef ArithLogic::getLeqForSort(SRef sr) const {
    assert(sr == getSort_int() or sr == getSort_real());
    return sr == getSort_int() ? get_sym_Int_LEQ() : get_sym_Real_LEQ();
}

// If the call results in a leq it is guaranteed that arg[0] is a
// constant, and arg[1][0] has factor 1 or -1
PTRef ArithLogic::mkBinaryLeq(PTRef lhs, PTRef rhs) {
    SRef argSort = checkArithSortCompatible({lhs, rhs});
    if (isConstant(lhs) && isConstant(rhs)) {
        opensmt::Number const & v1 = this->getNumConst(lhs);
        opensmt::Number const & v2 = this->getNumConst(rhs);
        return v1 <= v2 ? getTerm_true() : getTerm_false();
    }
    // Should be in the form that on one side there is a constant
    // and on the other there is a sum
    PTRef sum_tmp = lhs == getZeroForSort(argSort) ? rhs : rhs == getZeroForSort(argSort) ? mkNeg(lhs) : mkPlus(rhs, mkNeg(lhs));
    // "sum_tmp = rhs - lhs" so the inequality is "0 <= sum_tmp"
    if (isConstant(sum_tmp)) {
        opensmt::Number const & v = this->getNumConst(sum_tmp);
        return v.sign() < 0 ? getTerm_false() : getTerm_true();
    } if (isNumVarLike(sum_tmp) || isTimes(sum_tmp)) { // "sum_tmp = c * v", just scale to "v" or "-v" without changing the sign
        sum_tmp = isTimes(sum_tmp) ? normalizeMul(sum_tmp) : sum_tmp;
        return mkFun(getLeqForSort(argSort), {getZeroForSort(argSort), sum_tmp});
    } else if (isPlus(sum_tmp)) {
        // Normalize the sum
        return sumToNormalizedInequality(sum_tmp);
    }
    assert(false);
    throw OsmtInternalException{"Unexpected situation in LALogic::mkNumLeq"};
}

PTRef ArithLogic::mkLeq(vec<PTRef> const & args) {
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

PTRef ArithLogic::mkGeq(vec<PTRef> const & args) {
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

PTRef ArithLogic::mkLt(vec<PTRef> const & args)
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

PTRef ArithLogic::mkGt(vec<PTRef> const & args)
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
    if (getSortRef(rhs) != getSortRef(lhs)) { throw OsmtApiException("Equality over non-equal sorts"); }
    if (hasUFs()) { return Logic::mkBinaryEq(lhs, rhs); }
    SRef eqSort = getSortRef(lhs);
    if (!isSortNum(eqSort)) {
        return Logic::mkBinaryEq(lhs, rhs);
    }

    if (isConstant(lhs) && isConstant(rhs)) {
        opensmt::Number const & v1 = this->getNumConst(lhs);
        opensmt::Number const & v2 = this->getNumConst(rhs);
        return v1 == v2 ? getTerm_true() : getTerm_false();
    }

    // diff = rhs - lhs
    PTRef diff = isZero(lhs) ? rhs : isZero(rhs) ? mkNeg(lhs) : mkPlus(rhs, mkNeg(lhs));
    if (isConstant(diff)) {
        opensmt::Number const & v = this->getNumConst(diff);
        return v.isZero() ? getTerm_true() : getTerm_false();
    } else if (isNumVarLike(diff) || isTimes(diff)) {
        auto [var, constant] = splitTermToVarAndConst(diff);
        return Logic::mkBinaryEq(getZeroForSort(eqSort), var); // Avoid anything that calls Logic::mkEq as this would create a loop
    } else if (isPlus(diff)) {
        return sumToNormalizedEquality(diff);
    } else {
        assert(false);
        throw OsmtInternalException{"Unexpected situation in LALogic::mkNumLeq"};
    }
}

PTRef ArithLogic::mkMod(vec<PTRef> && args) {
    if (args.size() != 2) { throw OsmtApiException("Modulo needs exactly two arguments"); }
    checkSortInt(args);
    PTRef dividend = args[0];
    PTRef divisor = args[1];

    if (not isNumConst(divisor)) { throw OsmtApiException("Divisor must be constant in linear logic"); }
    if (isZero(divisor)) { throw ArithDivisionByZeroException(); }

    if (isConstant(dividend)) {
        auto const& dividendValue = getNumConst(dividend);
        auto const& divisorValue = getNumConst(divisor);
        assert(dividendValue.isInteger() and divisorValue.isInteger());
        // evaluate immediately the operation on two constants
        auto realDiv = dividendValue / divisorValue;
        auto intDiv = divisorValue.sign() > 0 ? realDiv.floor() : realDiv.ceil();
        auto intMod = dividendValue - intDiv * divisorValue;
        assert(intMod.sign() >= 0 and intMod < abs(divisorValue));
        return mkIntConst(intMod);
    }
    return mkFun(sym_Int_MOD, {dividend, divisor});
}

PTRef ArithLogic::mkIntDiv(vec<PTRef> && args) {
    checkSortInt(args);
    assert(args.size() == 2);
    PTRef dividend = args[0];
    PTRef divisor = args[1];
    if (not isConstant(divisor) and not isConstant(dividend)) { throw LANonLinearException("Divisor or dividend must be constant in linear logic"); }
    if (isZero(divisor)) { throw ArithDivisionByZeroException(); }

    if (isConstant(divisor) and isConstant(dividend)) {
        auto const& dividendValue = getNumConst(dividend);
        auto const& divisorValue = getNumConst(divisor);
        assert(dividendValue.isInteger() and divisorValue.isInteger());
        // evaluate immediately the operation on two constants
        auto realDiv = dividendValue / divisorValue;
        auto intDiv = divisorValue.sign() > 0 ? realDiv.floor() : realDiv.ceil();
        return mkIntConst(intDiv);
    }
    return mkFun(sym_Int_DIV, std::move(args));
}

PTRef ArithLogic::mkRealDiv(vec<PTRef> && args)
{
    checkSortReal(args);
    if (args.size() != 2) {
        throw OsmtApiException("Division operation requires exactly 2 arguments");
    }
    if (isZero(args[1])) {
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
        assert((isNumTerm(args_new[0]) || isPlus(args_new[0])) && isConstant(args_new[1]));
        args_new[1] = mkRealConst(FastRational_inverse(getNumConst(args_new[1]))); //mkConst(1/getRealConst(args_new[1]));
        return mkTimes(args_new);
    }
    PTRef tr = mkFun(s_new, std::move(args_new));
    return tr;
}

PTRef ArithLogic::insertTerm(SymRef sym, vec<PTRef>&& terms)
{
    if (isNeg(sym))
        return mkNeg(terms[0]);
    if (isMinus(sym))
        return mkMinus(std::move(terms));
    if (isPlus(sym))
        return mkPlus(std::move(terms));
    if (isTimes(sym))
        return mkTimes(std::move(terms));
    if (isRealDiv(sym))
        return mkRealDiv(std::move(terms));
    if (isLeq(sym))
        return mkLeq(terms);
    if (isLt(sym))
        return mkLt(terms);
    if (isGeq(sym))
        return mkGeq(terms);
    if (isGt(sym))
        return mkGt(terms);
    if (isMod(sym))
        return mkMod(std::move(terms));
    if (isIntDiv(sym))
        return mkIntDiv(std::move(terms));
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
        ptr = mkVar(s, rat, true);
        // Store the value of the number as a real
        SymId id = sym_store[getPterm(ptr).symb()].getId();
        for (auto i = numbers.size(); i <= id; i++)
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

    if (hasIntegers() and not hasReals()) {
        if (not isIntegralForm and isRealForm) {
            throw OsmtApiException("Expected integral constant");
        } else if (isIntegralForm) {
            return mkConst(sort_INT, name);
        }
    } else if (hasReals() and not hasIntegers()) {
        if (isRealForm) {
            return mkConst(sort_REAL, name);
        } else {
            assert(not isRealForm);
            throw OsmtApiException("Expected real constant");
        }
    } else {
        assert(hasReals() and hasIntegers());
        // Logic has mixed arithmetic
        if (isIntegralForm) {
            return mkConst(sort_INT, name);
        } else if (isRealForm) {
            return mkConst(sort_REAL, name);
        }
    }
    // Not a numeric constant, so let Logic decide.
    assert(not isRealForm and not isIntegralForm);
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
void SimplifyConst::simplify(SymRef s, vec<PTRef> const & args, SymRef & s_new, vec<PTRef> & args_new)
{
    vec<int> const_idx;
    for (int i = 0; i < args.size(); i++) {
        assert(!l.isNeg(args[i])); // MB: No minus nodes, the check can be simplified
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
    if (args_new.size() == 1 && (l.isPlus(s_new) || l.isTimes(s_new) )) {
        PTRef ch_tr = args_new[0];
        args_new.clear();
        s_new = l.getPterm(ch_tr).symb();
        for (int i = 0; i < l.getPterm(ch_tr).size(); i++)
            args_new.push(l.getPterm(ch_tr)[i]);
    }
}

void SimplifyConstSum::constSimplify(SymRef s, vec<PTRef> const & terms, SymRef & s_new, vec<PTRef> & terms_new) const
{
    assert(terms_new.size() == 0);
    for (auto tr : terms)
        if (not l.isZero(tr))
            terms_new.push(tr);
    if (terms_new.size() == 0) {
        // The term was sum of all zeroes
        terms_new.clear();
        s_new = l.getPterm(l.getZeroForSort(l.getSortRef(s))).symb();
        return;
    }
    s_new = s;
}

void SimplifyConstTimes::constSimplify(SymRef s, vec<PTRef> const & terms, SymRef & s_new, vec<PTRef> & terms_new) const
{
    PTRef con, plus;
    con = plus = PTRef_Undef;
    for (auto tr : terms) {
        if (l.isZero(tr)) {
            terms_new.clear();
            s_new = l.getPterm(l.getZeroForSort(l.getSortRef(s))).symb();
            return;
        }
        if ( not l.isOne(tr)) {
            if (l.isPlus(tr)) {
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
            sum_args.push(l.mkTimes(con, arg));
        }
        terms_new.push(l.mkPlus(std::move(sum_args)));
    }
    if (terms_new.size() == 0) {
        // The term was multiplication of all ones
        terms_new.clear();
        s_new = l.getPterm(l.getOneForSort(l.getSortRef(s))).symb();
        return;
    }
    s_new = s;
}

void SimplifyConstDiv::constSimplify(SymRef s, vec<PTRef> const & terms, SymRef & s_new, vec<PTRef> & terms_new) const
{
    assert(terms_new.size() == 0);
    assert(terms.size() <= 2);
    if (terms.size() == 2 && l.isZero(terms[1])) {
        printf("Explicit div by zero\n");
        assert(false);
    }
    if (terms.size() == 1 or l.isOne(terms[terms.size()-1])) {
        terms_new.clear();
        s_new = l.getPterm(terms[0]).symb();
        for (int i = 0; i < l.getPterm(terms[0]).size(); i++)
            terms_new.push(l.getPterm(terms[0])[i]);
        return;
    }
    else if (l.isZero(terms[0])) {
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
        return l.mkConst(l.getSortRef(terms[0]), s);
    } else if (terms.size() == 1) {
        return terms[0];
    } else {
        opensmt::Number s = l.getNumConst(terms[0]);
        for (int i = 1; i < terms.size(); i++) {
            assert(l.isConstant((terms[i])));
            opensmt::Number const& val = l.getNumConst(terms[i]);
            Op(s, val);
        }
        return l.mkConst(l.getSortRef(terms[0]), s);
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
    if (isSortNum(sref))
        return getZeroForSort(sref);
    else
        return Logic::getDefaultValuePTRef(sref);
}

PTRef ArithLogic::removeAuxVars(PTRef tr) {
    // Note: Since ites are removed first and div/mod's then, it is important to first reintroduce div/mod's and then ites
    class AuxSymbolMatcherConfig : public DefaultRewriterConfig {
        ArithLogic & logic;
    public:
        AuxSymbolMatcherConfig(ArithLogic & logic) : logic(logic) {}
        PTRef rewrite(PTRef tr) override {
            if (not logic.isVar(tr)) return tr; // Only variables can match
            auto symName = std::string_view(logic.getSymName(tr));
            if (symName.compare(0, DivModConfig::divPrefix.size(), DivModConfig::divPrefix) == 0) {
                return DivModConfig::getDivTermFor(logic, tr);
            } else if (symName.compare(0, DivModConfig::divPrefix.size(), DivModConfig::modPrefix) == 0){
                return DivModConfig::getModTermFor(logic, tr);
            }
            return tr;
        }
    };
    // Note: this has negligible impact on performance, no need to check if there are divs or mods
    AuxSymbolMatcherConfig config(*this);
    tr = Rewriter(*this, config).rewrite(tr);
    return Logic::removeAuxVars(tr);
}

// Handle the printing of real constants that are negative and the
// rational constants
std::string ArithLogic::printTerm_(PTRef tr, bool ext, bool safe) const
{
    if (isNumConst(tr)) {
        bool is_neg = false;
        char* tmp_str;
        opensmt::stringToRational(tmp_str, sym_store.getName(getPterm(tr).symb()));
        opensmt::Number v(tmp_str);
        if (!isNonNegNumConst(tr)) {
            v.negate();
            is_neg = true;
        }
        std::string rat_str = v.get_str();
        free(tmp_str);
        bool is_div = false;
        unsigned i = 0;
        unsigned rat_size = rat_str.size();
        for (; i != rat_size; i++) {
            if (rat_str[i] == '/') {
                is_div = true;
                break;
            }
        }
        if (is_div) {
            unsigned j = 0;
            char* nom = (char*) malloc(i+1);
            for (; j < i; j++)
                nom[j] = rat_str[j];
            nom[i] = '\0';
            char* den = (char*) malloc(rat_size-i);
            i++;
            j = 0;
            for (; i < rat_size; i++)
                den[j++] = rat_str[i];
            den[j] = '\0';
            char * tmp;
            std::stringstream str;
            int written = is_neg ? asprintf(&tmp, "(/ (- %s) %s)", nom, den)
                                 : asprintf(&tmp, "(/ %s %s)", nom, den);
            assert(written >= 0); (void)written;
            str << tmp;
            if (ext) {
                str << " <" << tr.x << ">";
            }
            free(nom);
            free(den);
            free(tmp);
            return str.str();
        }
        else if (is_neg) {
            std::stringstream str;
            str << "(- " << rat_str << ')';
            if (ext) {
                str << " <" << tr.x << ">";
            }
            return str.str();
        } else {
            return rat_str;
        }
    }
    return Logic::printTerm_(tr, ext, safe);
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
        auto [var, coeff] = splitTermToVarAndConst(factor);
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
            varFactors[i] = mkTimes(vars[i], mkConst(getSort_int(), coeffs[i]));
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
    auto [var, coeff] = splitTermToVarAndConst(leadingFactor);
    opensmt::Number normalizationCoeff = abs(getNumConst(coeff));
    // varFactors come from a normalized sum, no need to call normalization code again
    PTRef normalizedSum = varFactors.size() == 1 ? varFactors[0] : mkFun(get_sym_Real_PLUS(), std::move(varFactors));
    if (normalizationCoeff != 1) {
        // normalize the whole sum
        normalizedSum = mkTimes(normalizedSum, mkRealConst(normalizationCoeff.inverse()));
        // DON'T forget to update also the constant factor!
        constantValue /= normalizationCoeff;
    }
    constantValue.negate(); // moving the constant to the LHS of the inequality
    return {std::move(constantValue), normalizedSum};
}

opensmt::pair<FastRational, PTRef> ArithLogic::sumToNormalizedPair(PTRef sum) {
    SRef sr = getUniqueArgSort(sum);
    assert(isSortInt(sr) or isSortReal(sr));
    return isSortInt(sr) ? sumToNormalizedIntPair(sum) : sumToNormalizedRealPair(sum);
}

PTRef ArithLogic::sumToNormalizedInequality(PTRef sum) {
    auto [lhsVal, rhs] = sumToNormalizedPair(sum);
    SRef sort = getSortRef(rhs);
    if (isSortInt(sort)) { lhsVal = lhsVal.ceil(); }
    return mkFun(getLeqForSort(sort), {mkConst(sort, lhsVal), rhs});
}

PTRef ArithLogic::sumToNormalizedEquality(PTRef sum) {
    auto [lhsVal, rhs] = sumToNormalizedPair(sum);
    SRef sort = getSortRef(sum);
    if (isSortInt(sort) and not lhsVal.isInteger()) { return getTerm_false(); }
    return Logic::mkBinaryEq(mkConst(getSortRef(sum), lhsVal), rhs);
}

PTRef ArithLogic::getConstantFromLeq(PTRef leq) {
    Pterm const & term = getPterm(leq);
    if (not isLeq(term.symb())) {
        throw OsmtApiException("LALogic::getConstantFromLeq called on a term that is not less-or-equal inequality");
    }
    return term[0];
}

PTRef ArithLogic::getTermFromLeq(PTRef leq) {
    Pterm const & term = getPterm(leq);
    if (not isLeq(term.symb())) {
        throw OsmtApiException("LALogic::getConstantFromLeq called on a term that is not less-or-equal inequality");
    }
    return term[1];
}

std::pair<PTRef, PTRef> ArithLogic::leqToConstantAndTerm(PTRef leq) {
    Pterm const & term = getPterm(leq);
    assert(isLeq(term.symb()));
    return std::make_pair(term[0], term[1]);
}
