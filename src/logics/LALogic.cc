#include "SStore.h"
#include "PtStore.h"
#include "TreeOps.h"
#include "Global.h"
#include "LA.h"
#include "LALogic.h"
#include "FastRational.h"
#include "OsmtInternalException.h"

#include <memory>

bool LALogic::isNegated(PTRef tr) const {
    //static const opensmt::Integer zero = 0;
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

bool LALogic::isLinearFactor(PTRef tr) const {
    if (isNumConst(tr) || isNumVarOrIte(tr)) { return true; }
    if (isNumTimes(tr)) {
        Pterm const& term = getPterm(tr);
        return term.size() == 2 && ((isNumConst(term[0]) && (isNumVarOrIte(term[1])))
                                    || (isNumConst(term[1]) && (isNumVarOrIte(term[0]))));
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

void LALogic::splitTermToVarAndConst(const PTRef& term, PTRef& var, PTRef& fac) const
{
    assert(isNumTimes(term) || isNumDiv(term) || isNumVarOrIte(term) || isConstant(term) || isUF(term));
    if (isNumTimes(term) || isNumDiv(term)) {
        assert(getPterm(term).size() == 2);
        fac = getPterm(term)[0];
        var = getPterm(term)[1];
        if (!isConstant(fac)) {
            PTRef t = var;
            var = fac;
            fac = t;
        }
        assert(isConstant(fac));
        assert(isNumVarOrIte(var) || isUF(var));
    } else if (isNumVarOrIte(term) || isUF(term)) {
        var = term;
        fac = getTerm_NumOne();
    } else {
        var = PTRef_Undef; // MB: no variable
        fac = term;
    }
}

// Find the lexicographically first factor of a term and divide the other terms with it.
PTRef LALogic::normalizeSum(PTRef sum) {
    vec<PTRef> args;
    Pterm& s = getPterm(sum);
    for  (int i = 0; i < s.size(); i++)
        args.push(s[i]);
    termSort(args);
    PTRef const_term = PTRef_Undef;
    for (int i = 0; i < args.size(); i++) {
        if (isNumVar(args[i])) {
            // The lex first term has an implicit unit factor, no need to do anything.
            return sum;
        }
        if (isNumTimes(args[i])) {
            assert(!isNumZero(getPterm(args[i])[0]) && !isNumZero(getPterm(args[i])[1]));
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
    opensmt::Number k = abs(isConstant(t[0]) ? getNumConst(t[0]) : getNumConst(t[1]));
    // MB: the case (-1 * var) can get herem but we would be dividing by 1 here, no need for that
    if (k != 1) {
        PTRef divisor = mkConst(k);
        for (int i = 0; i < args.size(); i++) {
            vec<PTRef> tmp;
            tmp.push(args[i]);
            tmp.push(divisor);
            args[i] = mkNumDiv(tmp);
        }
    }
    // MB: There is nothing there to simplify anymore, since we just normalized constants, but the terms were normalized before
//    return mkNumPlus(args);
    return mkFun(get_sym_Num_PLUS(), args);
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
lbool LALogic::arithmeticElimination(const vec<PTRef> & top_level_arith, Map<PTRef, PtAsgn, PTRefHash> & substitutions)
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
        assert(var != PTRef_Undef && isNumVarOrIte(var) && sub.second != PTRef_Undef);
        if (substitutions.has(var)) {
            // Already has substitution for this var, let the main substitution code deal with this situation
            continue;
        } else {
            substitutions.insert(var, PtAsgn(sub.second, l_True));
        }
    }
    // To simplify this method, we do not try to detect a conflict here, so result is always l_Undef
    return l_Undef;
}
void LALogic::simplifyAndSplitEq(PTRef tr, PTRef& root_out)
{
    split_eq = true;
    simplifyTree(tr, root_out);
    split_eq = false;
}
lbool LALogic::retrieveSubstitutions(const vec<PtAsgn>& facts, Map<PTRef,PtAsgn,PTRefHash>& substs)
{
    lbool res = Logic::retrieveSubstitutions(facts, substs);
    if (res != l_Undef) return res;
    vec<PTRef> top_level_arith;
    for (int i = 0; i < facts.size(); i++) {
        PTRef tr = facts[i].tr;
        lbool sgn = facts[i].sgn;
        if (isNumEq(tr) && sgn == l_True)
            top_level_arith.push(tr);
    }
    return arithmeticElimination(top_level_arith, substs);
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
bool LALogic::okToPartition(PTRef tr) const
{
    return !la_split_inequalities.has(tr);
}

void LALogic::visit(PTRef tr, Map<PTRef,PTRef,PTRefHash>& tr_map)
{
    if (split_eq && isNumEq(tr)) {
        Pterm& p = getPterm(tr);
        PTRef a1 = p[0];
        PTRef a2 = p[1];
        vec<PTRef> args;
        args.push(a1); args.push(a2);
        PTRef i1 = mkNumLeq(args);
        PTRef i2 = mkNumGeq(args);
        args.clear();
        args.push(i1); args.push(i2);
        PTRef andr = mkAnd(args);
        la_split_inequalities.insert(i1, true);
        la_split_inequalities.insert(i2, true);
        assert(!tr_map.has(tr));
        tr_map.insert(tr, andr);
    }
    Logic::visit(tr, tr_map);
}

bool LALogic::isBuiltinFunction(const SymRef sr) const
{
    if (sr == get_sym_Num_NEG() || sr == get_sym_Num_MINUS() || sr == get_sym_Num_PLUS() || sr == get_sym_Num_TIMES() || sr == get_sym_Num_DIV() || sr == get_sym_Num_EQ() || sr == get_sym_Num_LEQ() || sr == get_sym_Num_LT() || sr == get_sym_Num_GEQ() || sr == get_sym_Num_GT() || sr == get_sym_Num_ITE()) return true;
    else return Logic::isBuiltinFunction(sr);
}
bool LALogic::isNumTerm(PTRef tr) const
{
    auto isNumVarOrUFOrIte = [this](PTRef tr) { return isNumVarOrIte(tr) || isUF(tr); };
    const Pterm& t = getPterm(tr);
    if (isNumVarOrIte(tr))
        return true;
    if (t.size() == 2 && isNumTimes(tr))
        return (isNumVarOrUFOrIte(t[0]) && isConstant(t[1])) || (isNumVarOrUFOrIte(t[1]) && isConstant(t[0]));
    else if (t.size() == 0)
        return isNumVar(tr) || isConstant(tr);
    else
        return false;
}

PTRef LALogic::mkNumNeg(PTRef tr, char** msg)
{
    assert(!isNumNeg(tr)); // MB: The invariant now is that there is no "Minus" node
    vec<PTRef> args;
    if (isNumPlus(tr)) {
        for (int i = 0; i < getPterm(tr).size(); i++) {
            PTRef tr_arg = mkNumNeg(getPterm(tr)[i], msg);
            assert(tr_arg != PTRef_Undef);
            args.push(tr_arg);
        }
        PTRef tr_n = mkFun(get_sym_Num_PLUS(), args);
        assert(tr_n == mkNumPlus(args, msg));
        assert(tr_n != PTRef_Undef);
        return tr_n;
    }
    if (isConstant(tr)) {
        const opensmt::Number& v = getNumConst(tr);
        opensmt::Number min = -v;
        PTRef nterm = mkConst(min);
        return nterm;
    }
    PTRef mo = this->getTerm_NumMinusOne();
    args.push(mo); args.push(tr);
    return mkNumTimes(args);
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

SRef   LALogic::getSort_num () const { return get_sort_NUM(); }
PTRef  LALogic::mkConst  (const char* num) { return mkConst(getSort_num(), num); }
PTRef  LALogic::mkNumVar (const char* name) { return mkVar(getSort_num(), name); }
bool LALogic::isBuiltinSort  (SRef sr) const { return sr == get_sort_NUM() || Logic::isBuiltinSort(sr); }
bool LALogic::isBuiltinConstant(SymRef sr) const { return (isNumConst(sr) || Logic::isBuiltinConstant(sr)); }
bool LALogic::isNumConst     (SymRef sr)     const { return Logic::isConstant(sr) && hasSortNum(sr); }
bool LALogic::isNumConst     (PTRef tr)      const { return isNumConst(getPterm(tr).symb()); }
bool LALogic::isNonnegNumConst (PTRef tr)  const { return isNumConst(tr) && getNumConst(tr) >= 0; }
bool LALogic::hasSortNum(SymRef sr) const { return sym_store[sr].rsort() == get_sort_NUM(); }
bool LALogic::hasSortNum(PTRef tr)  const { return hasSortNum(getPterm(tr).symb()); }
bool LALogic::isUFEquality(PTRef tr) const { return !isNumEq(tr) && Logic::isUFEquality(tr); }
bool LALogic::isTheoryEquality(PTRef tr) const { return isNumEq(tr); }
bool LALogic::isAtom(PTRef tr) const  { return isNumEq(tr) || isNumLt(tr) || isNumGt(tr) || isNumLeq(tr) || isNumGeq(tr) || Logic::isAtom(tr); }
bool LALogic::isUF(PTRef tr) const { return isUF(term_store[tr].symb()); }
bool LALogic::isUF(SymRef sr) const { return !sym_store[sr].isInterpreted(); }
bool LALogic::isNumPlus(SymRef sr) const { return sr == get_sym_Num_PLUS(); }
bool LALogic::isNumPlus(PTRef tr) const { return isNumPlus(getPterm(tr).symb()); }
bool LALogic::isNumMinus(SymRef sr) const { return sr == get_sym_Num_MINUS(); }
bool LALogic::isNumMinus(PTRef tr) const { return isNumMinus(getPterm(tr).symb()); }
bool LALogic::isNumNeg(SymRef sr) const { return sr == get_sym_Num_NEG(); }
bool LALogic::isNumNeg(PTRef tr) const { return isNumNeg(getPterm(tr).symb()); }
bool LALogic::isNumTimes(SymRef sr) const { return sr == get_sym_Num_TIMES(); }
bool LALogic::isNumTimes(PTRef tr) const { return isNumTimes(getPterm(tr).symb()); }
bool LALogic::isNumDiv(SymRef sr) const { return sr == get_sym_Num_DIV(); }
bool LALogic::isNumDiv(PTRef tr) const { return isNumDiv(getPterm(tr).symb()); }
bool LALogic::isNumEq(SymRef sr) const { return isEquality(sr) && (sym_store[sr][0] == get_sort_NUM());}
bool LALogic::isNumEq(PTRef tr) const { return isNumEq(getPterm(tr).symb()); }
bool LALogic::isNumLeq(SymRef sr) const { return sr == get_sym_Num_LEQ(); }
bool LALogic::isNumLeq(PTRef tr) const { return isNumLeq(getPterm(tr).symb()); }
bool LALogic::isNumLt(SymRef sr) const { return sr == get_sym_Num_LT(); }
bool LALogic::isNumLt(PTRef tr) const { return isNumLt(getPterm(tr).symb()); }
bool LALogic::isNumGeq(SymRef sr) const { return sr == get_sym_Num_GEQ(); }
bool LALogic::isNumGeq(PTRef tr) const { return isNumGeq(getPterm(tr).symb()); }
bool LALogic::isNumGt(SymRef sr) const { return sr == get_sym_Num_GT(); }
bool LALogic::isNumGt(PTRef tr) const { return isNumGt(getPterm(tr).symb()); }
bool LALogic::isNumVar(SymRef sr) const { return isVar(sr) && sym_store[sr].rsort() == get_sort_NUM(); }
bool LALogic::isNumVarOrIte(SymRef sr) const { return isNumVar(sr) || isIte(sr); }
bool LALogic::isNumVarOrIte(PTRef tr) const { return isNumVarOrIte(getPterm(tr).symb()); }
bool LALogic::isNumVar(PTRef tr) const { return isNumVar(getPterm(tr).symb()); }
bool LALogic::isNumZero(SymRef sr) const { return sr == get_sym_Num_ZERO(); }
bool LALogic::isNumZero(PTRef tr) const { return tr == getTerm_NumZero(); }
bool LALogic::isNumOne(SymRef sr) const { return sr == get_sym_Num_ONE(); }
bool LALogic::isNumOne(PTRef tr) const { return tr == getTerm_NumOne(); }

//PTRef mkNumNeg(PTRef, char **);
PTRef LALogic::mkNumNeg(PTRef tr) {
    char *msg;
    PTRef trn = mkNumNeg(tr, &msg);
    assert(trn != PTRef_Undef);
    return trn;
}
PTRef mkNumMinus(const vec<PTRef> &, char **);
PTRef LALogic::mkNumMinus(const vec<PTRef> &args) {
    char *msg;
    PTRef tr = mkNumMinus(args, &msg);
    assert(tr != PTRef_Undef);
    return tr;
}
PTRef LALogic::mkNumMinus(const PTRef a1, const PTRef a2) {
    vec<PTRef> tmp;
    tmp.push(a1);
    tmp.push(a2);
    return mkNumMinus(tmp);
}

PTRef LALogic::mkNumPlus(const PTRef p1, const PTRef p2) {
    vec<PTRef> tmp {p1, p2};
    return mkNumPlus(tmp);
}

PTRef LALogic::mkNumPlus(const vec<PTRef> &args) {
    char *msg;
    PTRef tr = mkNumPlus(args, &msg);
    assert(tr != PTRef_Undef);
    return tr;
}
PTRef LALogic::mkNumPlus(const std::vector<PTRef> &args) {
    vec<PTRef> tmp;
    for (PTRef arg : args) { tmp.push(arg); }
    return mkNumPlus(tmp);
}

PTRef LALogic::mkNumTimes(const vec<PTRef> &args) {
    char *msg;
    PTRef tr = mkNumTimes(args, &msg);
    assert(tr != PTRef_Undef);
    return tr;
}
PTRef LALogic::mkNumTimes(const PTRef p1, const PTRef p2) {
    vec<PTRef> tmp;
    tmp.push(p1);
    tmp.push(p2);
    return mkNumTimes(tmp);
}
PTRef LALogic::mkNumTimes(const std::vector<PTRef> &args) {
    vec<PTRef> tmp;
    for (PTRef arg : args) { tmp.push(arg); }
    return mkNumTimes(tmp);
}
PTRef mkNumDiv(const vec<PTRef> &, char **);
PTRef LALogic::mkNumDiv(const vec<PTRef> &args) {
    char *msg;
    PTRef tr = mkNumDiv(args, &msg);
    assert(tr != PTRef_Undef);
    return tr;
}
PTRef LALogic::mkNumDiv(const PTRef nom, const PTRef den) {
    vec<PTRef> tmp;
    tmp.push(nom), tmp.push(den);
    return mkNumDiv(tmp);
}

PTRef LALogic::mkNumLeq(const vec<PTRef> &args) {
    assert(args.size() == 2);
    PTRef tr = mkNumLeq(args[0], args[1]);
    assert(tr != PTRef_Undef);
    return tr;
}

PTRef LALogic::mkNumGeq(const PTRef arg1, const PTRef arg2) {
    return mkNumLeq(arg2, arg1);
}

PTRef LALogic::mkNumLt(const PTRef arg1, const PTRef arg2) {
    vec<PTRef> tmp;
    tmp.push(arg1);
    tmp.push(arg2);
    return mkNumLt(tmp);
}

PTRef LALogic::mkNumGt(const PTRef arg1, const PTRef arg2) {
    vec<PTRef> tmp;
    tmp.push(arg1);
    tmp.push(arg2);
    return mkNumGt(tmp);
}

char* LALogic::printTerm(PTRef tr) const { return printTerm_(tr, false, false); }
char* LALogic::printTerm(PTRef tr, bool l, bool s) const { return printTerm_(tr, l, s); }
PTRef LALogic::mkNumMinus(const vec<PTRef>& args_in, char** msg)
{
    vec<PTRef> args;
    args_in.copyTo(args);
    if (args.size() == 1) {
        return mkNumNeg(args[0], msg);
    }
    assert (args.size() == 2);
    PTRef mo = mkConst(getSort_num(), "-1");
    if (mo == PTRef_Undef) {
        printf("Error: %s\n", *msg);
        assert(false);
    }
    vec<PTRef> tmp;
    tmp.push(mo);
    tmp.push(args[1]);
    PTRef fact = mkNumTimes(tmp, msg);
    if (fact == PTRef_Undef) {
        printf("Error: %s\n", *msg);
        assert(false);
    }
    args[1] = fact;
    return mkNumPlus(args);
}

PTRef LALogic::mkNumPlus(const vec<PTRef>& args, char** msg)
{
    vec<PTRef> new_args;
    new_args.capacity(args.size());
    // Flatten possible internal sums.  This needs not be done properly,
    // with a post-order dfs, since we are guaranteed that the inner
    // sums are already flattened.
    for (int i = 0; i < args.size(); i++) {
        if (isNumPlus(args[i])) {
            Pterm& t = getPterm(args[i]);
            for (int j = 0; j < t.size(); j++)
                new_args.push(t[j]);
        } else {
            new_args.push(args[i]);
        }
    }
    SimplifyConstSum simp(*this);
    vec<PTRef> args_new;
    SymRef s_new;
    simp.simplify(get_sym_Num_PLUS(), new_args, s_new, args_new, msg);
    if (args_new.size() == 1)
        return args_new[0];
    if (s_new != get_sym_Num_PLUS()) {
        return mkFun(s_new, args_new);
    }
    // This code takes polynomials (+ (* v c1) (* v c2)) and converts them to the form (* v c3) where c3 = c1+c2
    VecMap<PTRef,PTRef,PTRefHash> s2t;
    vec<PTRef> keys;
    for (int i = 0; i < args_new.size(); ++i) {
        PTRef v;
        PTRef c;
        splitTermToVarAndConst(args_new[i], v, c);
        assert(c != PTRef_Undef);
        assert(isConstant(c));
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
        const vec<PTRef>& consts = s2t[keys[i]];
        PTRef consts_summed = consts.size() == 1 ? consts[0] : mkNumPlus(consts);
        if (isNumZero(consts_summed)) { continue; }
        if (keys[i] == PTRef_Undef) {
            sum_args.push(consts_summed);
            continue;
        }
        if (isNumOne(consts_summed)) {
            sum_args.push(keys[i]);
            continue;
        }
        // default case, variable and constant (cannot be simplified)
        vec<PTRef> term_args;
        term_args.push(consts_summed);
        term_args.push(keys[i]);
        PTRef term = mkFun(get_sym_Num_TIMES(), term_args);
        sum_args.push(term);
    }
    if (sum_args.size() == 0) return getTerm_NumZero();
    if (sum_args.size() == 1) return sum_args[0];
    PTRef tr = mkFun(s_new, sum_args);
    return tr;
}
PTRef LALogic::mkNumTimes(const vec<PTRef>& tmp_args, char** msg)
{
    vec<PTRef> args;
    // Flatten possible internal multiplications
    for (int i = 0; i < tmp_args.size(); i++) {
        if (isNumTimes(tmp_args[i])) {
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
    simp.simplify(get_sym_Num_TIMES(), args, s_new, args_new, msg);
    PTRef tr = mkFun(s_new, args_new);
    // Either a real term or, if we constructed a multiplication of a
    // constant and a sum, a real sum.
    if (isNumTerm(tr) || isNumPlus(tr) || isUF(tr) || isIte(tr))
        return tr;
    else {
        throw LANonLinearException(printTerm(tr));
    }
}

PTRef LALogic::mkNumDiv(const vec<PTRef>& args, char** msg)
{
    SimplifyConstDiv simp(*this);
    vec<PTRef> args_new;
    SymRef s_new;
    assert(args.size() == 2);
    if(this->isNumZero(args[1])) {
        throw LADivisionByZeroException();
    }
    simp.simplify(get_sym_Num_DIV(), args, s_new, args_new, msg);
    if (isNumDiv(s_new)) {
        assert((isNumTerm(args_new[0]) || isNumPlus(args_new[0])) && isConstant(args_new[1]));
        args_new[1] = mkConst(FastRational_inverse(getNumConst(args_new[1]))); //mkConst(1/getRealConst(args_new[1]));
        return mkNumTimes(args_new);
    }
    PTRef tr = mkFun(s_new, args_new);
    return tr;
}

// If the call results in a leq it is guaranteed that arg[0] is a
// constant, and arg[1][0] has factor 1 or -1
PTRef LALogic::mkNumLeq(PTRef lhs, PTRef rhs)
{
    if (isConstant(lhs) && isConstant(rhs)) {
        opensmt::Number const & v1 = this->getNumConst(lhs);
        opensmt::Number const & v2 = this->getNumConst(rhs);
        if (v1 <= v2)
            return getTerm_true();
        else
            return getTerm_false();
    }
    // Should be in the form that on one side there is a constant
    // and on the other there is a sum
    PTRef sum_tmp = [&](){
       if (lhs == getTerm_NumZero()) { return rhs; }
       if (rhs == getTerm_NumZero()) { return mkNumNeg(lhs); }
       vec<PTRef> sum_args;
       sum_args.push(rhs);
       sum_args.push(mkNumNeg(lhs));
       return mkNumPlus(sum_args);
    }(); // now the inequality is "0 <= sum_tmp" where "sum_tmp = rhs - lhs"
    if (isConstant(sum_tmp)) {
        opensmt::Number const & v = this->getNumConst(sum_tmp);
        return v.sign() < 0 ? getTerm_false() : getTerm_true();
    } if (isNumVarOrIte(sum_tmp) || isNumTimes(sum_tmp)) { // "sum_tmp = c * v", just scale to "v" or "-v" without changing the sign
        sum_tmp = isNumTimes(sum_tmp) ? normalizeMul(sum_tmp) : sum_tmp;
        vec<PTRef> args;
        args.push(getTerm_NumZero());
        args.push(sum_tmp);
        return mkFun(get_sym_Num_LEQ(), args);
    } else if (isNumPlus(sum_tmp)) {
        // Normalize the sum
        return sumToNormalizedInequality(sum_tmp);
    }
    assert(false);
    throw OsmtInternalException{"Unexpected situation in LALogic::mkNumLeq"};
}

PTRef LALogic::mkNumGeq(const vec<PTRef> & args)
{
    assert(args.size() == 2);
    return mkNumLeq(args[1], args[0]);
}
PTRef LALogic::mkNumLt(const vec<PTRef> & args)
{
    if (isConstant(args[0]) && isConstant(args[1])) {
        opensmt::Number const& v1 = this->getNumConst(args[0]);
        opensmt::Number const& v2 = this->getNumConst(args[1]);
        if (v1 < v2) {
            return getTerm_true();
        } else {
            return getTerm_false();
        }
    }
    PTRef tr = mkNumLeq(args[1], args[0]);
    if (tr == PTRef_Undef) {
//        printf("%s\n", *msg);
        assert(false);
    }
    return mkNot(tr);
}
PTRef LALogic::mkNumGt(const vec<PTRef> & args)
{
    PTRef tr = mkNumLeq(args);
    if (tr == PTRef_Undef) {
        assert(false);
    }
    return mkNot(tr);
}
PTRef LALogic::insertTerm(SymRef sym, vec<PTRef>& terms, char **msg)

{
    if (sym == get_sym_Num_NEG())
        return mkNumNeg(terms[0], msg);
    if (sym == get_sym_Num_MINUS())
        return mkNumMinus(terms, msg);
    if (sym == get_sym_Num_PLUS())
        return mkNumPlus(terms, msg);
    if (sym == get_sym_Num_TIMES())
        return mkNumTimes(terms, msg);
    if (sym == get_sym_Num_DIV())
        return mkNumDiv(terms, msg);
    if (sym == get_sym_Num_LEQ())
        return mkNumLeq(terms);
    if (sym == get_sym_Num_LT())
        return mkNumLt(terms);
    if (sym == get_sym_Num_GEQ())
        return mkNumGeq(terms);
    if (sym == get_sym_Num_GT())
        return mkNumGt(terms);
    if (sym == get_sym_Num_ITE())
        return mkIte(terms);
    return Logic::insertTerm(sym, terms, msg);
}
PTRef LALogic::mkConst(const char *name, const char **msg)
{
    return mkConst(getSort_num(), name);
}
PTRef LALogic::mkConst(SRef s, const char* name)
{
    assert(strlen(name) != 0);
    PTRef ptr = PTRef_Undef;
    if (s == get_sort_NUM()) {
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
void SimplifyConst::simplify(const SymRef& s, const vec<PTRef>& args, SymRef& s_new, vec<PTRef>& args_new, char** msg)
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
            if (tr == PTRef_Undef) {
                printf("%s\n", *msg);
                assert(false);
            }
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
    if (args_new.size() == 1 && (l.isNumPlus(s_new) || l.isNumTimes(s_new) || l.isNumDiv(s_new))) {
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
        for(int i = 0; i < termSize; ++i)
        {
            vec<PTRef> times_args;
            times_args.push(con);
            // MB: we cannot use Pterm& here, because in the line after next new term might be allocated, which might
            //     trigger reallocation of the table of terms
            times_args.push(l.getPterm(plus)[i]);
            sum_args.push(l.mkNumTimes(times_args));
        }
        terms_new.push(l.mkNumPlus(sum_args));
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
    if (l.isNumOne(terms[terms.size()-1])) {
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

LALogic::LALogic() :
    Logic()
        , split_eq(false)
{}


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

PTRef LALogic::sumToNormalizedInequality(PTRef sum) {
    assert(isNumPlus(sum));
    vec<PTRef> varFactors;
    PTRef constant = PTRef_Undef;
    Pterm const & s = getPterm(sum);
    for (int i = 0; i < s.size(); i++) {
        if (isConstant(s[i])) {
            assert(constant == PTRef_Undef);
            constant = s[i];
        } else {
            assert(isLinearFactor(s[i]));
            varFactors.push(s[i]);
        }
    }

    if (constant == PTRef_Undef) { constant = getTerm_NumZero(); }
    opensmt::Number constantVal = getNumConst(constant);
    assert(varFactors.size() > 0);
    termSort(varFactors);
    PTRef leadingFactor = varFactors[0];
    // normalize the sum according to the leading factor
    PTRef var, coeff;
    splitTermToVarAndConst(leadingFactor, var, coeff);
    opensmt::Number normalizationCoeff = abs(getNumConst(coeff));
    // varFactors come from a normalized sum, no need to call normalization code again
    PTRef normalizedSum = varFactors.size() == 1 ? varFactors[0] : insertTermHash(get_sym_Num_PLUS(), varFactors);
    if (normalizationCoeff != 1) {
        // normalize the whole sum
         normalizedSum = mkNumTimes(normalizedSum, mkConst(normalizationCoeff.inverse()));
        // DON'T forget to update also the constant factor!
        constantVal /= normalizationCoeff;
    }
    constantVal.negate(); // moving the constant to the LHS of the inequality
    return insertTermHash(get_sym_Num_LEQ(), {mkConst(constantVal), normalizedSum});
}

void SimplifyConstSum::Op(opensmt::Number& s, const opensmt::Number& v) const { s += v; }
opensmt::Number SimplifyConstSum::getIdOp() const { return 0; }
void SimplifyConstTimes::Op(opensmt::Number& s, const opensmt::Number& v) const { s *= v; }
opensmt::Number SimplifyConstTimes::getIdOp() const { return 1; }
void SimplifyConstDiv::Op(opensmt::Number& s, const opensmt::Number& v) const { if (v == 0) { printf("explicit div by zero\n"); } s /= v; }
opensmt::Number SimplifyConstDiv::getIdOp() const { return 1; }


