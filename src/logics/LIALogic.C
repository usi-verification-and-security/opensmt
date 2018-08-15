#include "SStore.h"
#include "PtStore.h"
#include "LIALogic.h"
#include "LALogic.h"
#include "TreeOps.h"
#include "Global.h"
#include "LA.h"
const char* LIALogic::e_nonlinear_term = "Logic does not support nonlinear terms";
//make sure you call all methods neede for each LIA and LRA here and override it properly
/*
void LIALogic::termSort(vec<PTRef>& v) const
{
    sort(v, LIALessThan_deepPTRef(this));
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
    if (args_new.size() == 1 && (l.isIntPlus(s_new) || l.isIntTimes(s_new))) {
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

void LIASimplifyConstTimes::constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const
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

 */
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

const char* LIALogic::s_sort_integer = "Int";

LIALogic::LIALogic(SMTConfig& c) :
        LALogic(c)
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
/*
bool LIALogic::isBuiltinFunction(const SymRef sr) const
{
    if (sr == sym_Int_NEG || sr == sym_Int_MINUS || sr == sym_Int_PLUS || sr == sym_Int_TIMES || sr == sym_Int_DIV || sr == sym_Int_EQ || sr == sym_Int_LEQ || sr == sym_Int_LT || sr == sym_Int_GEQ || sr == sym_Int_GT || sr == sym_Int_ITE) return true;
    else return LALogic::isBuiltinFunction(sr);
}
 */

/*
const opensmt::Integer2&
LIALogic::getIntegerConst(PTRef tr) const
{
    SymId id = sym_store[getPterm(tr).symb()].getId();
    assert(id < integers.size() && integers[id] != NULL);
    return *integers[id];
}*/

const char*   LIALogic::getName()         const  { return getLogic().str; }
const Logic_t LIALogic::getLogic()        const  { return QF_LIA; }
bool LIALogic::isBuiltinSort(SRef sr) const  { return sr == sort_INTEGER || Logic::isBuiltinSort(sr); }
bool  LIALogic::isNonnegNumConst(PTRef tr) const  { return isNumConst(tr) && getNumConst(tr) >= 0; }

//SRef   declareSort_Integer(char** msg);
SRef   LIALogic::getSort_num()  const  {return sort_INTEGER;}

//const opensmt::Number& LIALogic::getNumConst(PTRef tr) const  {return getIntegerConst(tr);}


bool        LIALogic::isIntPlus(SymRef sr)  const { return sr == sym_Int_PLUS; }
//bool      isIntPlus(PTRef tr)   const { return isIntPlus(getPterm(tr).symb()); }
bool        LIALogic::isNumPlus(PTRef tr)   const  { return isIntPlus(getPterm(tr).symb()); }
bool        LIALogic::isIntMinus(SymRef sr) const { return sr == sym_Int_MINUS; }
//bool      isIntMinus(PTRef tr)  const { return isIntMinus(getPterm(tr).symb()); }
bool        LIALogic::isNumMinus(PTRef tr)  const  { return isIntMinus(getPterm(tr).symb()); }
bool        LIALogic::isIntNeg(SymRef sr)   const { return sr == sym_Int_NEG; }
//bool      isIntNeg(PTRef tr)    const { return isIntNeg(getPterm(tr).symb()); }
bool        LIALogic::isNumNeg(PTRef tr)    const  { return isIntNeg(getPterm(tr).symb()); }
bool        LIALogic::isIntTimes(SymRef sr) const { return sr == sym_Int_TIMES; }
//bool      isIntTimes(PTRef tr)  const { return isIntTimes(getPterm(tr).symb()); }
bool        LIALogic::isNumTimes(PTRef tr)  const  { return isIntTimes(getPterm(tr).symb()); }
bool        LIALogic::isIntDiv(SymRef sr)   const { return sr == sym_Int_DIV; }
//bool        isIntDiv(PTRef tr)    const { return isIntDiv(getPterm(tr).symb()); }
bool        LIALogic::isNumDiv(PTRef tr)    const  { return isIntDiv(getPterm(tr).symb()); }
bool        LIALogic::isIntEq(SymRef sr)    const { return isEquality(sr) && (sym_store[sr][0] == sort_INTEGER); }
//bool      isIntEq(PTRef tr)     const { return isIntEq(getPterm(tr).symb()); }
bool        LIALogic::isNumEq(PTRef tr)     const  { return isIntEq(getPterm(tr).symb()); }
bool        LIALogic::isIntLeq(SymRef sr)   const { return sr == sym_Int_LEQ; }
//bool      isIntLeq(PTRef tr)    const { return isIntLeq(getPterm(tr).symb()); }
bool        LIALogic::isNumLeq(PTRef tr)    const  { return isIntLeq(getPterm(tr).symb()); }
bool        LIALogic::isIntLt(SymRef sr)    const { return sr == sym_Int_LT; }
//bool      isIntLt(PTRef tr)     const { return isIntLt(getPterm(tr).symb()); }
bool        LIALogic::isNumLt(PTRef tr)     const  { return isIntLt(getPterm(tr).symb()); }
bool        LIALogic::isIntGeq(SymRef sr)   const { return sr == sym_Int_GEQ; }
//bool      isIntGeq(PTRef tr)    const { return isIntGeq(getPterm(tr).symb()); }
bool        LIALogic::isNumGeq(PTRef tr)    const  { return isIntGeq(getPterm(tr).symb()); }
bool        LIALogic::isIntGt(SymRef sr)    const { return sr == sym_Int_GT; }
//bool      isIntGt(PTRef tr)     const { return isIntGt(getPterm(tr).symb()); }
bool        LIALogic::isNumGt(PTRef tr)     const  { return isIntGt(getPterm(tr).symb()); }
bool        LIALogic::isIntVar(SymRef sr)   const { return isVar(sr) && sym_store[sr].rsort() == sort_INTEGER; }
//bool      isIntVar(PTRef tr)    const { return isIntVar(getPterm(tr).symb()); }
bool        LIALogic::isNumVar(PTRef tr)    const  { return isIntVar(getPterm(tr).symb());}
//bool      isIntMod(SymRef sr)   const { return sr == sym_Int_MOD; }
//bool      isIntMod(PTRef tr)    const { return isIntMod(getPterm(tr).symb()); }
//bool      isIntABS(SymRef sr)   const { return sr == sym_int_ABS; }
//bool      isIntABS(PTRef tr)    const { return isIntABS(getPterm(tr).symb()); }
bool        LIALogic::isIntZero(SymRef sr)  const { return sr == sym_Int_ZERO; }
//bool      isIntZero(PTRef tr)   const { return tr == term_Int_ZERO; }
bool        LIALogic::isNumZero(PTRef tr)   const  { return tr == term_Int_ZERO; }
bool        LIALogic::isIntOne(SymRef sr)   const { return sr == sym_Int_ONE; }
//bool      isIntOne(PTRef tr)    const { return tr == term_Int_ONE; }
bool        LIALogic::isNumOne(PTRef tr)    const  { return tr == term_Int_ONE; }
bool        LIALogic::hasSortInt(SymRef sr) const { return sym_store[sr].rsort() == sort_INTEGER; }
bool        LIALogic::hasSortNum(PTRef tr) const  { return hasSortInt(getPterm(tr).symb()); }
PTRef       LIALogic::getTerm_NumZero() const  { return term_Int_ZERO; }
PTRef      LIALogic::getTerm_NumOne()  const  { return term_Int_ONE; }


const SymRef LIALogic::get_sym_Num_TIMES () const {return sym_Int_TIMES;}
const  SymRef LIALogic::get_sym_Num_DIV () const {return sym_Int_DIV;}
const  SymRef LIALogic::get_sym_Num_MINUS () const {return sym_Int_MINUS;}
const SymRef LIALogic::get_sym_Num_PLUS () const {return sym_Int_PLUS;}
const SymRef LIALogic::get_sym_Num_NEG () const {return sym_Int_NEG;}
const SymRef LIALogic::get_sym_Num_LEQ () const {return sym_Int_LEQ;}
const SymRef LIALogic::get_sym_Num_GEQ () const {return sym_Int_GEQ;}
const SymRef LIALogic::get_sym_Num_LT () const {return sym_Int_LT;}
const SymRef LIALogic::get_sym_Num_GT () const {return sym_Int_GT;}
const SymRef LIALogic::get_sym_Num_EQ () const {return sym_Int_EQ;}
const SymRef LIALogic::get_sym_Num_ZERO () const {return sym_Int_ZERO;}
const SymRef LIALogic::get_sym_Num_ONE () const {return sym_Int_ONE;}
const SymRef LIALogic::get_sym_Num_ITE () const {return sym_Int_ITE;}
const SRef LIALogic::get_sort_NUM () const {return sort_INTEGER;}