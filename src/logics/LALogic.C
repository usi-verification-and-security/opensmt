#include "SStore.h"
#include "PtStore.h"
#include "TreeOps.h"
#include "Global.h"
#include "LA.h"
#include "LALogic.h"
#include "FastRational.h"
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
    else {
        // Cases(3)
        return isNegated(getPterm(tr)[0]);
    }
}
const opensmt::Number&
LALogic::getNumConst(PTRef tr) const
{
    SymId id = sym_store[getPterm(tr).symb()].getId();
    assert(id < numbers.size() && numbers[id] != NULL);
    return *numbers[id];
}
void LALogic::splitTermToVarAndConst(const PTRef& term, PTRef& var, PTRef& fac) const
{
    assert(isNumTimes(term) || isNumDiv(term) || isNumVar(term) || isConstant(term) || isUF(term));
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
        assert(isNumVar(var) || isUF(var));
    } else if (isNumVar(term) || isUF(term)) {
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
    opensmt::Number r = getNumConst(c); //PS. shall I add opensmt::Integer j = getNumConst(c)
    if (r < 0) //PS. OR (l < 0)
        return mkNumNeg(v);
    else
        return v;
}
lbool LALogic::arithmeticElimination(const vec<PTRef> & top_level_arith, Map<PTRef, PtAsgn, PTRefHash> & substitutions)
{
    vec<LAExpression*> equalities;
    LALogic& logic = *this;
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
        char *msg;
        Pterm& p = getPterm(tr);
        PTRef a1 = p[0];
        PTRef a2 = p[1];
        vec<PTRef> args;
        args.push(a1); args.push(a2);
        PTRef i1 = mkNumLeq(args, &msg);
        PTRef i2 = mkNumGeq(args, &msg);
        args.clear();
        args.push(i1); args.push(i2);
        PTRef andr = mkAnd(args);
#ifdef PRODUCE_PROOF
        const ipartitions_t &part = getIPartitions(tr);
        transferPartitionMembership(tr, andr);
        addIPartitions(i1, part);
        addIPartitions(i2, part);
#endif
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
    const Pterm& t = getPterm(tr);
    if (t.size() == 2 && isNumTimes(tr))
        return ((isNumVar(t[0]) || isUF(t[0])) && isConstant(t[1])) || ((isNumVar(t[1]) || isUF(t[1])) && isConstant(t[0]));
    else if (t.size() == 0)
        return isNumVar(tr) || isConstant(tr);
    else
        return false;
}

PTRef LALogic::mkNumNeg(PTRef tr, char** msg)
{
    if (isNumNeg(tr)) return getPterm(tr)[0];
    vec<PTRef> args;
    if (isNumPlus(tr)) {
        for (int i = 0; i < getPterm(tr).size(); i++) {
            PTRef tr_arg = mkNumNeg(getPterm(tr)[i], msg);
            assert(tr_arg != PTRef_Undef);
            args.push(tr_arg);
        }
        PTRef tr_n = mkNumPlus(args, msg);
        assert(tr_n != PTRef_Undef);
        return tr_n;
    }
    if (isConstant(tr)) {
//        char * rat_str;
//        opensmt::stringToRational(rat_str, sym_store.getName(getPterm(tr).symb()));
//        opensmt::Number v(rat_str);
//        //PTRef nterm = getNTerm(rat_str); //PS. getNTerm generalise line 358, 361, 362
//        free(rat_str);
//        v = -v;
//        PTRef nterm = mkConst(getSort_num(), v.get_str().c_str());
//        SymRef s = getPterm(nterm).symb();
//        return mkFun(s, args, msg);
        const opensmt::Number& v = getNumConst(tr);
        opensmt::Number min = -v;
        PTRef nterm = mkConst(min);
        return nterm;
    }
    PTRef mo = mkConst(getSort_num(), "-1");
    args.push(mo); args.push(tr);
    return mkNumTimes(args);
}

PTRef  LALogic::mkConst(const opensmt::Number& c)
//{ char* rat; opensmt::stringToRational(rat, c.get_str().c_str()); PTRef tr = mkConst(getSort_num(), rat); free(rat); return tr; }
{
    std::string str = c.get_str(); // MB: I cannot store c.get_str().c_str() directly, since that is a pointer inside temporary object -> crash.
    const char * val = str.c_str();
    PTRef ptr = PTRef_Undef;
    ptr = mkVar(getSort_num(), val);
    // Store the value of the number as a real
    SymId id = sym_store[getPterm(ptr).symb()].getId();
    for (int i = numbers.size(); i <= id; i++) { numbers.push(nullptr); }
    if (numbers[id] == nullptr) { numbers[id] = new opensmt::Number(val); }
    assert(c == *numbers[id]);
    // Code to allow efficient constant detection.
    while (id >= constants.size())
        constants.push(false);
    constants[id] = true;
    return ptr;
}

SRef   LALogic::getSort_num () const { return get_sort_NUM(); }
PTRef  LALogic::mkConst  (const char* num) { return mkConst(getSort_num(), num); }
PTRef  LALogic::mkNumVar (const char* name) { return mkVar(getSort_num(), name); }
bool LALogic::isBuiltinSort  (SRef sr) const { return sr == get_sort_NUM() || Logic::isBuiltinSort(sr); }
bool LALogic::isBuiltinConstant(SymRef sr) const { return (isNumConst(sr) || Logic::isBuiltinConstant(sr)); }
bool LALogic::isNumConst     (SymRef sr)     const { return isConstant(sr) && hasSortNum(sr); }
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
//PTRef mkNumPlus(const vec<PTRef> &, char **);
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
    char *msg;
    PTRef tr = mkNumLeq(args, &msg);
    assert(tr != PTRef_Undef);
    return tr;
}
PTRef LALogic::mkNumLeq(const PTRef arg1, const PTRef arg2) {
    vec<PTRef> tmp;
    tmp.push(arg1);
    tmp.push(arg2);
    return mkNumLeq(tmp);
}

PTRef LALogic::mkNumGeq(const vec<PTRef> &args) {
    char *msg;
    PTRef tr = mkNumGeq(args, &msg);
    assert(tr != PTRef_Undef);
    return tr;
}
PTRef LALogic::mkNumGeq(const PTRef arg1, const PTRef arg2) {
    vec<PTRef> tmp;
    tmp.push(arg1);
    tmp.push(arg2);
    return mkNumGeq(tmp);
}

PTRef LALogic::mkNumLt(const vec<PTRef> &args) {
    char *msg;
    PTRef tr = mkNumLt(args, &msg);
    assert(tr != PTRef_Undef);
    return tr;
}
PTRef LALogic::mkNumLt(const PTRef arg1, const PTRef arg2) {
    vec<PTRef> tmp;
    tmp.push(arg1);
    tmp.push(arg2);
    return mkNumLt(tmp);
}

PTRef LALogic::mkNumGt(const vec<PTRef> &args) {
    char *msg;
    PTRef tr = mkNumGt(args, &msg);
    assert(tr != PTRef_Undef);
    return tr;
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
    SymRef s;
    vec<PTRef> args;
    args_in.copyTo(args);
    if (args.size() == 1) {
        return mkNumNeg(args[0], msg);
//        s = sym_Real_NEG;
//        return mkFun(s, args, msg);
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
    if(s_new != get_sym_Num_PLUS()) {
        return mkFun(s_new, args_new, msg);
    }
    // This code takes polynomials (+ (* v c1) (* v c2)) and converts them to the form (* v c3) where c3 = c1+c2
    VecMap<PTRef,PTRef,PTRefHash> s2t;
    vec<PTRef> keys;
    for (int i = 0; i < args_new.size(); ++i) {
        PTRef v;
        PTRef c;
        splitTermToVarAndConst(args_new[i], v, c);
        assert(isConstant(c));
        if (c == PTRef_Undef) {
            // The term is unit
            c = getTerm_NumOne();
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
    PTRef tr = mkFun(s_new, sum_args, msg);
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
    PTRef tr = mkFun(s_new, args_new, msg);
    // Either a real term or, if we constructed a multiplication of a
    // constant and a sum, a real sum.
    if (isNumTerm(tr) || isNumPlus(tr) || isUF(tr))
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
    PTRef tr = mkFun(s_new, args_new, msg);
    return tr;
}
// If the call results in a leq it is guaranteed that arg[0] is a
// constant, and arg[1][0] has factor 1 or -1
PTRef LALogic::mkNumLeq(const vec<PTRef>& args_in, char** msg)
{
    vec<PTRef> args;
    args_in.copyTo(args);
    assert(args.size() == 2);
    if (isConstant(args[0]) && isConstant(args[1])) {
        opensmt::Number v1(sym_store.getName(getPterm(args[0]).symb()));
        opensmt::Number v2(sym_store.getName(getPterm(args[1]).symb()));
        if (v1 <= v2) //PS. OR (v3<=v4)
            return getTerm_true();
        else
            return getTerm_false();
    } else {
        // Should be in the form that on one side there is a constant
        // and on the other there is a sum
        PTRef sum_tmp = [&](){
           if (args[0] == getTerm_NumZero()) {return args[1];}
           if (args[1] == getTerm_NumZero()) {return mkNumNeg(args[0]);}
           vec<PTRef> sum_args;
           sum_args.push(args[1]);
           sum_args.push(mkNumNeg(args[0]));
           return mkNumPlus(sum_args);
        }();
        if (isConstant(sum_tmp)) {
            args[0] = getTerm_NumZero();
            args[1] = sum_tmp;
            return mkNumLeq(args, msg); // either true or false
        } if (isNumTimes(sum_tmp)) {
            sum_tmp = normalizeMul(sum_tmp);
        } else if (isNumPlus(sum_tmp)) {
            // Normalize the sum
            sum_tmp = normalizeSum(sum_tmp); //Now the sum is normalized by dividing with the "first" factor.
        }
        // Otherwise no operation, already normalized
        vec<PTRef> nonconst_args;
        PTRef c = PTRef_Undef;
        if (isNumPlus(sum_tmp)) {
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
                args[0] = getTerm_NumZero();
                args[1] = mkNumPlus(nonconst_args);
            } else {
                args[0] = mkNumNeg(c);
                args[1] = mkNumPlus(nonconst_args);
            }
        } else if (isNumVar(sum_tmp) || isNumTimes(sum_tmp)) {
            args[0] = getTerm_NumZero();
            args[1] = sum_tmp;
        } else assert(false);
        PTRef r = mkFun(get_sym_Num_LEQ(), args, msg);
        return r;
    }
}
PTRef LALogic::mkNumGeq(const vec<PTRef>& args, char** msg)
{
    vec<PTRef> new_args;
    new_args.push(args[1]);
    new_args.push(args[0]);
    return mkNumLeq(new_args, msg);
}
PTRef LALogic::mkNumLt(const vec<PTRef>& args, char** msg)
{
    if (isConstant(args[0]) && isConstant(args[1])) {
        char *rat_str1, *rat_str2;
        opensmt::stringToRational(rat_str1, sym_store.getName(getPterm(args[0]).symb()));
        opensmt::stringToRational(rat_str2, sym_store.getName(getPterm(args[1]).symb()));
        opensmt::Number v1(rat_str1);
        opensmt::Number v2(rat_str2);
        free(rat_str1);
        free(rat_str2);
        if (v1 < v2) { //PS. OR (v3 < v4)
            return getTerm_true();
        } else {
            return getTerm_false();
        }
    }
    vec<PTRef> tmp;
    tmp.push(args[1]);
    tmp.push(args[0]);
    PTRef tr = mkNumLeq(tmp, msg);
    if (tr == PTRef_Undef) {
        printf("%s\n", *msg);
        assert(false);
    }
    return mkNot(tr);
}
PTRef LALogic::mkNumGt(const vec<PTRef>& args, char** msg)
{
    if (isConstant(args[0]) && isConstant(args[1])) {
        char *rat_str1, *rat_str2;
        opensmt::stringToRational(rat_str1, sym_store.getName(getPterm(args[0]).symb()));
        opensmt::stringToRational(rat_str2, sym_store.getName(getPterm(args[1]).symb()));
        opensmt::Number v1(rat_str1);
        opensmt::Number v2(rat_str2);
        free(rat_str1);
        free(rat_str2);
        if (v1 > v2) //PS. OR (v3 > v4)
            return getTerm_true();
        else
            return getTerm_false();
    }
    PTRef tr = mkNumLeq(args, msg);
    if (tr == PTRef_Undef) {
        printf("%s\n", *msg);
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
        return mkNumLeq(terms, msg);
    if (sym == get_sym_Num_LT())
        return mkNumLt(terms, msg);
    if (sym == get_sym_Num_GEQ())
        return mkNumGeq(terms, msg);
    if (sym == get_sym_Num_GT())
        return mkNumGt(terms, msg);
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
        for (int i = numbers.size(); i <= id; i++)
            numbers.push(nullptr);
        if (numbers[id] != nullptr) { delete numbers[id]; }
        numbers[id] = new opensmt::Number(rat);
        free(rat);
        // Code to allow efficient constant detection.
        while (id >= constants.size())
            constants.push(false);
        constants[id] = true;
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
    vec<PTRef> args_new_2;
    for (int i = 0; i < args.size(); i++) {
        if (l.isConstant(args[i]) || (l.isNumNeg(args[i]) && l.isConstant(l.getPterm(args[i])[0])))
            const_idx.push(i);
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
    //distribute the constant over the first sum
    int i;
    PTRef con, plus;
    con = plus = PTRef_Undef;
    for (i = 0; i < terms.size(); i++) {
        if (l.isNumZero(terms[i])) {
            terms_new.clear();
            s_new = l.getPterm(l.getTerm_NumZero()).symb();
            return;
        }
        if (!l.isNumOne(terms[i]))
        {
            if(l.isNumPlus(terms[i]))
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
        return l.mkConst(l.getSort_num(), s.get_str().c_str());
    } else if (terms.size() == 1) {
        char* rat_str;
        opensmt::stringToRational(rat_str, l.getSymName(terms[0]));
        opensmt::Number val(rat_str);
        free(rat_str);
        return l.mkConst(l.getSort_num(), val.get_str().c_str());
    } else {
        char* rat_str;
        opensmt::stringToRational(rat_str, l.getSymName(terms[0]));
        opensmt::Number s(rat_str);
        free(rat_str);
        for (int i = 1; i < terms.size(); i++) {
            PTRef tr = PTRef_Undef;
            if (l.isConstant(terms[i]))
                tr = terms[i];
            else if (l.isNumNeg(terms[i]))
                tr = l.getPterm(terms[i])[0];
            else continue;
            char* rat_str;
            opensmt::stringToRational(rat_str, l.getSymName(tr));
            opensmt::Number val(rat_str);
            free(rat_str);
            Op(s, val);
        }
        return l.mkConst(l.getSort_num(), s.get_str().c_str());
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

LALogic::LALogic(SMTConfig& c) :
        Logic(c)
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

void SimplifyConstSum::Op(opensmt::Number& s, const opensmt::Number& v) const { s += v; }
opensmt::Number SimplifyConstSum::getIdOp() const { return 0; }
void SimplifyConstTimes::Op(opensmt::Number& s, const opensmt::Number& v) const { s *= v; }
opensmt::Number SimplifyConstTimes::getIdOp() const { return 1; }
void SimplifyConstDiv::Op(opensmt::Number& s, const opensmt::Number& v) const { if (v == 0) { printf("explicit div by zero\n"); } s /= v; }
opensmt::Number SimplifyConstDiv::getIdOp() const { return 1; }


