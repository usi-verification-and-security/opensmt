/*******************************************************************\
Module: New Logic for BitVector

 *  Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Author: Sepideh Asadi <sepideh.a65@gmail.com>
 *  Created on: Jan 16, 2017
\*******************************************************************/

#include "SStore.h"
#include "PtStore.h"
#include "BVLogic.h"
#include "CUFLogic.h"
#include "TreeOps.h"
#include "Global.h"

int BVLogic::tk_bv_zero  = 0;
int BVLogic::tk_bv_one   = 1;
const char* BVLogic::tk_bv_neg   = "-";
const char* BVLogic::tk_bv_minus = "-";
const char* BVLogic::tk_bv_plus  = "+";
const char* BVLogic::tk_bv_times = "*";
const char* BVLogic::tk_bv_div   = "/";
const char* BVLogic::tk_bv_lt    = "<";
const char* BVLogic::tk_bv_leq   = "<=";
const char* BVLogic::tk_bv_gt    = ">";
const char* BVLogic::tk_bv_geq   = ">=";

const char* BVLogic::tk_bv_lshift = "<<";
const char* BVLogic::tk_bv_rshift = ">>";
const char* BVLogic::tk_bv_mod    = "%";
const char* BVLogic::tk_bv_bwand  = "&";
const char* BVLogic::tk_bv_bwor   = "|";
const char* BVLogic::tk_bv_inc    = "++";
const char* BVLogic::tk_bv_dec    = "--";
const char* BVLogic::tk_bv_neq    = "!=";
const char* BVLogic::tk_bv_land   = "&&";
const char* BVLogic::tk_bv_lor    = "||";
const char* BVLogic::tk_bv_not    = "!";
const char* BVLogic::tk_bv_bwxor  = "^";
const char* BVLogic::tk_bv_compl  = "~";
const char* BVLogic::tk_bv_sizeof = "sizeof";
const char* BVLogic::tk_bv_addrof = "&";
const char* BVLogic::tk_bv_ptr    = "*";
const char* BVLogic::tk_bv_cond   = "?";

const char*  BVLogic::s_sort_bvnum = "BVNum";
//const char*  BVLogic::s_sort_bvstr = "BVStr";

BVLogic::BVLogic(SMTConfig& c) :
      Logic(c)
    , sym_BV_ZERO(SymRef_Undef)
    , sym_BV_ONE(SymRef_Undef)
    , sym_BV_NEG(SymRef_Undef)
    , sym_BV_MINUS(SymRef_Undef)
    , sym_BV_PLUS(SymRef_Undef)
    , sym_BV_TIMES(SymRef_Undef)
    , sym_BV_DIV(SymRef_Undef)
    , sym_BV_EQ(SymRef_Undef)
    , sym_BV_LEQ(SymRef_Undef)
    , sym_BV_LT(SymRef_Undef)
    , sym_BV_GEQ(SymRef_Undef)
    , sym_BV_GT(SymRef_Undef)
    , sort_BVNUM(SRef_Undef)
    , term_BV_ZERO(PTRef_Undef)
    , term_BV_ONE(PTRef_Undef)
{
    logic_type = opensmt::QF_BV;
    char* msg;
    sort_BVNUM = declareSort(s_sort_bvnum, &msg);

    vec<SRef> params;
    term_BV_ZERO = mkConst(tk_bv_zero);
    sym_BV_ZERO  = getSymRef(term_BV_ZERO);
    term_BV_ONE  = mkConst(tk_bv_one);
    sym_BV_ONE   = getSymRef(term_BV_ONE);

    params.push(sort_BVNUM);

    // Unary
    sym_BV_NEG    = declareFun(tk_bv_neg, sort_BVNUM, params, &msg, true);
    sym_BV_INC    = declareFun(tk_bv_inc, sort_BVNUM, params, &msg, true);
    sym_BV_DEC    = declareFun(tk_bv_dec, sort_BVNUM, params, &msg, true);
    sym_BV_COMPL  = declareFun(tk_bv_compl, sort_BVNUM, params, &msg, true);
    sym_BV_SIZEOF = declareFun(tk_bv_sizeof, sort_BVNUM, params, &msg, true);
    sym_BV_ADDROF = declareFun(tk_bv_addrof, sort_BVNUM, params, &msg, true);
    sym_BV_PTR    = declareFun(tk_bv_ptr, sort_BVNUM, params, &msg, true);

    params.push(sort_BVNUM);

    // Binary
    sym_BV_MINUS = declareFun(tk_bv_neg, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_MINUS].setLeftAssoc();

    sym_BV_PLUS  = declareFun(tk_bv_plus, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_PLUS].setNoScoping();
    sym_store[sym_BV_PLUS].setCommutes();
    sym_store[sym_BV_PLUS].setLeftAssoc();

    sym_BV_TIMES = declareFun(tk_bv_times, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_TIMES].setNoScoping();
    sym_store[sym_BV_TIMES].setLeftAssoc();
    sym_store[sym_BV_TIMES].setCommutes();

    sym_BV_DIV   = declareFun(tk_bv_div, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_DIV].setNoScoping();
    sym_store[sym_BV_DIV].setLeftAssoc();

    sym_BV_LEQ  = declareFun(tk_bv_leq, sort_BOOL, params, &msg, true);
    sym_store[sym_BV_LEQ].setNoScoping();
    sym_store[sym_BV_LEQ].setChainable();

    sym_BV_LT   = declareFun(tk_bv_lt, sort_BOOL, params, &msg, true);
    sym_store[sym_BV_LT].setNoScoping();
    sym_store[sym_BV_LT].setChainable();

    sym_BV_GEQ  = declareFun(tk_bv_geq, sort_BOOL, params, &msg, true);
    sym_store[sym_BV_GEQ].setNoScoping();
    sym_store[sym_BV_GEQ].setChainable();

    sym_BV_GT   = declareFun(tk_bv_gt, sort_BOOL, params, &msg, true);
    sym_store[sym_BV_GEQ].setNoScoping();
    sym_store[sym_BV_GEQ].setChainable();

    sym_BV_NEQ    = declareFun(tk_bv_neq, sort_BOOL, params, &msg, true);
    sym_store[sym_BV_NEQ].setCommutes();

    sym_BV_LAND   = declareFun(tk_bv_land, sort_BOOL, params, &msg, true);
    sym_store[sym_BV_LAND].setCommutes();

    sym_BV_LOR    = declareFun(tk_bv_lor, sort_BOOL, params, &msg, true);
    sym_store[sym_BV_LOR].setCommutes();

    sym_BV_LSHIFT = declareFun(tk_bv_lshift, sort_BVNUM, params, &msg, true);
    sym_BV_RSHIFT = declareFun(tk_bv_rshift, sort_BVNUM, params, &msg, true);

    sym_BV_MOD    = declareFun(tk_bv_mod, sort_BVNUM, params, &msg, true);
    sym_BV_BWAND  = declareFun(tk_bv_bwand, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_BWAND].setCommutes();

    sym_BV_BWOR   = declareFun(tk_bv_bwor, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_BWOR].setCommutes();
}

BVLogic::~BVLogic()
{}

//PTRef
//BVLogic::insertTerm(SymRef sym, vec<PTRef>& terms, char **msg)
//{
//    assert(false);
//    return PTRef_Undef;
//}

PTRef
BVLogic::mkBVNeg(PTRef tr, char** msg)
{
    if (isBVNeg(tr)) return getPterm(tr)[0];
    if (isConstant(tr)) {
        int v = atoi(sym_store.getName(getPterm(tr).symb()));
        v = -v;
        PTRef nterm = mkConst(v);
      /*  SymRef s = getPterm(nterm).symb();
        vec<PTRef> args;
        args.push(nterm);
        return mkFun(s, args, msg);*/
        return nterm;
    }
    vec<PTRef> arg;
    arg.push(tr);
    tr = mkFun(sym_BV_NEG, arg, msg);
    return  tr;
}

PTRef
BVLogic::mkBVMinus(const vec<PTRef>& args_in, char** msg)
{
    SymRef s;
    vec<PTRef> args;
    args_in.copyTo(args);
    if (args.size() == 1)
        return mkBVNeg(args[0], msg);

    assert(args.size() == 2);
    PTRef mo = mkConst(-1);
    vec<PTRef> tmp;
    PTRef fact = mkBVTimes(mo, args[1], msg);
    args[1] = fact;
    return mkBVPlus(args[0], args[1]);
}

PTRef
BVLogic::mkBVPlus(const PTRef arg1, const PTRef arg2, char** msg)
{
    vec<PTRef> sum_args;
    sum_args.push(arg1);
    sum_args.push(arg2);
    PTRef tr = mkFun(sym_BV_PLUS, sum_args, msg);
//    sum_args[0] = arg2;
//    sum_args[1] = arg1;
//    PTRef tr_comm = mkFun(sym_BV_PLUS, sum_args, msg);
//    PTRef tr_comm_eq = mkEq(tr, tr_comm);
//    if (!comm_eqs.has(tr_comm_eq))
//        comm_eqs.insert(tr_comm_eq, true);
    return tr;
}


PTRef
BVLogic::mkBVTimes(const PTRef arg1, const PTRef arg2, char** msg)
{
    vec<PTRef> times_args;
    times_args.push(arg1);
    times_args.push(arg2);

    PTRef tr = mkFun(sym_BV_TIMES, times_args, msg);
//    times_args[0] = arg2;
//    times_args[1] = arg1;
//    PTRef tr_comm = mkFun(sym_BV_TIMES, times_args, msg);
//    PTRef tr_comm_eq = mkEq(tr, tr_comm);
//    if (!comm_eqs.has(tr_comm_eq))
//        comm_eqs.insert(tr_comm_eq, true);
    return tr;
}

PTRef
BVLogic::mkBVDiv(const PTRef arg1, const PTRef arg2)
{
    vec<PTRef> div_args;
    div_args.push(arg1);
    div_args.push(arg2);
    char** msg;
    PTRef tr = mkFun(sym_BV_DIV, div_args, msg);
    return tr;
}

PTRef
BVLogic::mkBVGeq(const PTRef arg1, const PTRef arg2, char** msg)
{
    return mkBVLeq(arg2, arg1, msg);
}

PTRef
BVLogic::mkBVLeq(const PTRef arg1, const PTRef arg2, char** msg)
{
    if (isBVNUMConst(arg1) && isBVNUMConst(arg2)) {
        int c1 = getBVNUMConst(arg1);
        int c2 = getBVNUMConst(arg2);
        if (c1 <= c2)
            return getTerm_true();
        else
            return getTerm_false();
    }
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    return mkFun(sym_BV_LEQ, args, msg);
}

PTRef
BVLogic::mkBVGt(const PTRef arg1, const PTRef arg2, char** msg)
{
    if (isBVNUMConst(arg1) && isBVNUMConst(arg2)) {
        int c1 = getBVNUMConst(arg1);
        int c2 = getBVNUMConst(arg2);
        if (c1 > c2)
            return getTerm_true();
        else
            return getTerm_false();
    }
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    PTRef tr = mkFun(sym_BV_GT, args, msg);
    // a>b -> a != b
 //   PTRef tr_eq = mkEq(arg1, arg2);
//    PTRef n_tr_eq = mkBVNot(tr_eq);
//    PTRef tr_impl = mkImpl(n_tr_eq, n_tr_eq);
//    if (!diseq_eqs.has(tr_impl))
//        diseq_eqs.insert(tr_impl, true);
    return tr;
}

PTRef BVLogic::mkBVLt(const PTRef arg1, const PTRef arg2, char** msg)
{
    return mkBVGt(arg2, arg1, msg);
}

PTRef BVLogic::mkBVLshift(const PTRef arg1, const PTRef arg2)
{
    if (isBVNUMConst(arg2) && getBVNUMConst(arg2) == 0)
        return arg1;
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    char** msg;
    return mkFun(sym_BV_LSHIFT, args, msg);
}

PTRef BVLogic::mkBVRshift(const PTRef arg1, const PTRef arg2)
{
    if (isBVNUMConst(arg2) && getBVNUMConst(arg2) == 0)
        return arg1;
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    char** msg;
    return mkFun(sym_BV_RSHIFT, args, msg);
}

PTRef BVLogic::mkBVMod(const PTRef arg1, const PTRef arg2)
{
    if (isBVNUMConst(arg2) && getBVNUMConst(arg2) == 1)
        return getTerm_BVZero();
    // if b > 0, then 0 <= a % b < b
    // if b < 0, then b < a % b <= 0
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    char** msg;

    return mkFun(sym_BV_MOD, args, msg);
}

PTRef BVLogic::mkBVBwAnd(const PTRef arg1, const PTRef arg2)
{
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    char** msg;
    return mkFun(sym_BV_BWAND, args, msg);
}

PTRef BVLogic::mkBVBwOr(const PTRef arg1, const PTRef arg2)
{
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    char** msg;
    return mkFun(sym_BV_BWOR, args, msg);
}

/*PTRef BVLogic::mkBVInc(const PTRef arg1)
{
    vec<PTRef> args;
    args.push(arg1);
    char** msg;
    PTRef tr = mkFun(sym_BV_INC, args, msg);
//    PTRef neq = mkBVNeq(arg1, tr);
//    if (!inc_diseqs.has(neq))
//        inc_diseqs.insert(neq, true);
    return tr;
}

PTRef BVLogic::mkBVDec(const PTRef arg1)
{
    vec<PTRef> args;
    args.push(arg1);
    char** msg;
    PTRef tr = mkFun(sym_BV_DEC, args, msg);
//    PTRef neq = mkBVNeq(arg1, tr);
//    if (!inc_diseqs.has(neq))
//        inc_diseqs.insert(neq, true);
    return tr;
}*/

PTRef BVLogic::mkBVLand(const PTRef arg1, const PTRef arg2)
{
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    char** msg;
    PTRef tr = mkFun(sym_BV_LAND, args, msg);
    return tr;
}

PTRef BVLogic::mkBVLor(const PTRef arg1, const PTRef arg2)
{
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    char** msg;
    PTRef tr = mkFun(sym_BV_LOR, args, msg);
    return tr;
}

PTRef BVLogic::mkBVNot(const PTRef arg)
{
    return Logic::mkNot(arg);
}

PTRef BVLogic::mkBVBwxor(const PTRef arg1, const PTRef arg2)
{
    char** msg;
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    return mkFun(sym_BV_BWXOR, args, msg);
}

PTRef BVLogic::mkBVCompl(const PTRef arg1)
{
    vec<PTRef> args;
    args.push(arg1);
    char** msg;
    PTRef tr = mkFun(sym_BV_COMPL, args, msg);
//    PTRef neq = mkBVNeq(tr, arg1);
//    if (!compl_diseqs.has(neq))
//        compl_diseqs.insert(neq, true);
    return tr;
}
/*
PTRef BVLogic::mkBVSizeof(const PTRef arg)
{
    vec<PTRef> args;
    args.push(arg);
    char** msg;
    return mkFun(sym_BV_SIZEOF, args, msg);
}

PTRef BVLogic::mkBVAddrof(const PTRef arg)
{
    vec<PTRef> args;
    args.push(arg);
    char** msg;
    return mkFun(sym_BV_SIZEOF, args, msg);
}


PTRef BVLogic::mkBVPtr(const PTRef arg)
{
    vec<PTRef> args;
    args.push(arg);
    char** msg;
    return mkFun(sym_BV_PTR, args, msg);
}*/

/*PTRef BVLogic::mkBVCond(const PTRef cond, PTRef i_arg, PTRef e_arg)
{
    return mkIte(cond, i_arg, e_arg);
}*/
PTRef BVLogic::mkBVEq(const PTRef a1, const PTRef a2) {
    if(isConstant(a1) && isConstant(a2))
        return (a1 == a2) ? getTerm_true() : getTerm_false();
    if (a1 == a2) return getTerm_true();
    char** msg;
    vec<PTRef> args;
    args.push(a1);
    args.push(a2);
    return mkFun(sym_BV_EQ, args, msg);
}

PTRef BVLogic::mkBVNeq(const PTRef a1, const PTRef a2)
{
	vec<PTRef> args;
	args.push(a1);
	args.push(a2);
    return mkBVNeg(mkBVEq(args));
}

const int BVLogic::getBVNUMConst(PTRef tr) const
{
    return atoi(getSymName(tr));
}

/*void BVLogic::conjoinExtras(PTRef root, PTRef& root_out)
{
    vec<PTRef> comm_eqs;
    vec<PTRef> diseq_eqs;
    vec<PTRef> diseq_split;
    vec<PTRef> mod_ineqs;
    vec<PTRef> inc_diseqs;
    vec<PTRef> compl_diseqs;
    getCommEqs(comm_eqs);
    getCommEqs(diseq_eqs);
    getCommEqs(diseq_split);
    getCommEqs(mod_ineqs);
    getCommEqs(inc_diseqs);
    getCommEqs(compl_diseqs);
    root_out = root;
    root_out = mkAnd(root_out, mkAnd(comm_eqs));
    root_out = mkAnd(root_out, mkAnd(diseq_eqs));
    root_out = mkAnd(root_out, mkAnd(diseq_split));
    root_out = mkAnd(root_out, mkAnd(mod_ineqs));
    root_out = mkAnd(root_out, mkAnd(inc_diseqs));
    root_out = mkAnd(root_out, mkAnd(compl_diseqs));
    Logic::conjoinItes(root_out, root_out);
}*/




