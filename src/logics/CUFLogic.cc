/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2017 Antti Hyvarinen

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
#include "CUFLogic.h"
#include "TreeOps.h"
#include "Global.h"

const char* CUFLogic::tk_cuf_zero  = "0";
const char* CUFLogic::tk_cuf_one   = "1";
const char* CUFLogic::tk_cuf_neg   = "-";
const char* CUFLogic::tk_cuf_minus = "-";
const char* CUFLogic::tk_cuf_plus  = "+";
const char* CUFLogic::tk_cuf_times = "*";
const char* CUFLogic::tk_cuf_div   = "/";
const char* CUFLogic::tk_cuf_lt    = "<";
const char* CUFLogic::tk_cuf_leq   = "<=";
const char* CUFLogic::tk_cuf_gt    = ">";
const char* CUFLogic::tk_cuf_geq   = ">=";

const char* CUFLogic::tk_cuf_lshift = "<<";
const char* CUFLogic::tk_cuf_lrshift = "l>>";
const char* CUFLogic::tk_cuf_arshift = "a>>";
const char* CUFLogic::tk_cuf_mod    = "%";
const char* CUFLogic::tk_cuf_bwand  = "&";
const char* CUFLogic::tk_cuf_bwor   = "|";
const char* CUFLogic::tk_cuf_inc    = "++";
const char* CUFLogic::tk_cuf_dec    = "--";
const char* CUFLogic::tk_cuf_neq    = "!=";
const char* CUFLogic::tk_cuf_land   = "&&";
const char* CUFLogic::tk_cuf_lor    = "||";
const char* CUFLogic::tk_cuf_not    = "!";
const char* CUFLogic::tk_cuf_bwxor  = "^";
const char* CUFLogic::tk_cuf_compl  = "~";
const char* CUFLogic::tk_cuf_sizeof = "sizeof";
const char* CUFLogic::tk_cuf_addrof = "&";
const char* CUFLogic::tk_cuf_ptr    = "*";
const char* CUFLogic::tk_cuf_cond   = "?";

const char*  CUFLogic::s_sort_cufnum = "CUFNum";

CUFLogic::CUFLogic(opensmt::Logic_t logicType) :
      Logic(logicType)
    , sort_CUFNUM(declareUninterpretedSort(s_sort_cufnum))
    , term_CUF_ZERO(mkConst(sort_CUFNUM, tk_cuf_zero))
    , term_CUF_ONE(mkConst(sort_CUFNUM, tk_cuf_one))
    , sym_CUF_ZERO(getSymRef(term_CUF_ZERO))
    , sym_CUF_ONE(getSymRef(term_CUF_ONE))
    , sym_CUF_NEG(declareFun_NoScoping(tk_cuf_neg, sort_CUFNUM, {sort_CUFNUM}))
    , sym_CUF_MINUS(declareFun_NoScoping_LeftAssoc(tk_cuf_minus, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_PLUS(declareFun_NoScoping_LeftAssoc(tk_cuf_plus, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_TIMES(declareFun_NoScoping_LeftAssoc(tk_cuf_times, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_DIV(declareFun_NoScoping_LeftAssoc(tk_cuf_div, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_MOD(declareFun_NoScoping(tk_cuf_mod, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_EQ(sortToEquality[sort_CUFNUM])
    , sym_CUF_LEQ(declareFun_NoScoping_Chainable(tk_cuf_leq, sort_BOOL, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_LT(declareFun_NoScoping_Chainable(tk_cuf_lt, sort_BOOL, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_GEQ(declareFun_NoScoping_Chainable(tk_cuf_geq, sort_BOOL, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_GT(declareFun_NoScoping_Chainable(tk_cuf_gt, sort_BOOL, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_LSHIFT(declareFun_NoScoping_LeftAssoc(tk_cuf_lshift, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_LRSHIFT(declareFun_NoScoping_LeftAssoc(tk_cuf_lrshift, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_ARSHIFT(declareFun_NoScoping_LeftAssoc(tk_cuf_arshift, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_BWAND(declareFun_NoScoping_LeftAssoc(tk_cuf_bwand, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_BWOR(declareFun_NoScoping_LeftAssoc(tk_cuf_bwor, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_INC(declareFun_NoScoping(tk_cuf_inc, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_DEC(declareFun_NoScoping(tk_cuf_dec, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_NEQ(declareFun_Commutative_NoScoping_Chainable(tk_equals, sort_BOOL, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_LAND(declareFun_NoScoping_LeftAssoc(tk_cuf_land, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_LOR(declareFun_NoScoping_LeftAssoc(tk_cuf_lor, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_BWXOR(declareFun_Commutative_NoScoping_LeftAssoc(tk_cuf_bwxor, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_COMPL(declareFun_Commutative_NoScoping_LeftAssoc(tk_cuf_bwxor, sort_CUFNUM, {sort_CUFNUM, sort_CUFNUM}))
    , sym_CUF_SIZEOF(declareFun_NoScoping(tk_cuf_sizeof, sort_CUFNUM, {sort_CUFNUM}))
    , sym_CUF_ADDROF(declareFun_NoScoping(tk_cuf_addrof, sort_CUFNUM, {sort_CUFNUM}))
    , sym_CUF_PTR(declareFun_NoScoping(tk_cuf_addrof, sort_CUFNUM, {sort_CUFNUM}))
    , sym_CUF_ITE(sortToIte[sort_CUFNUM])
    , sym_CUF_DISTINCT(sortToDisequality[sort_CUFNUM])
{ }

CUFLogic::~CUFLogic()
{}

//PTRef
//CUFLogic::insertTerm(SymRef sym, vec<PTRef>& terms, char **msg)
//{
//    assert(false);
//    return PTRef_Undef;
//}

PTRef
CUFLogic::mkCUFNeg(PTRef tr)
{
    if (isCUFNeg(tr)) return getPterm(tr)[0];
    if (isCUFPlus(tr)) {
        vec<PTRef> args;
        assert(getPterm(tr).size() == 2);
        PTRef arg1 = mkCUFNeg(getPterm(tr)[0]);
        PTRef arg2 = mkCUFNeg(getPterm(tr)[1]);
        PTRef tr_n = mkCUFPlus(arg1, arg2);
        assert(tr_n != PTRef_Undef);
        return tr_n;
    }
    if (isConstant(tr)) {
        int v = getCUFNUMConst(tr);
        v = -v;
        PTRef nterm = mkCUFConst(v);
        SymRef s = getPterm(nterm).symb();
        return mkFun(s, {});
    }
    PTRef mo = mkCUFConst(-1);
    return mkCUFTimes(mo, tr);
}

PTRef
CUFLogic::mkCUFMinus(const vec<PTRef>& args_in)
{
    vec<PTRef> args;
    args_in.copyTo(args);
    if (args.size() == 1) {
        PTRef ret = mkCUFNeg(args[0]);
        return ret;
    }
    else {
        assert(args.size() == 2);
        PTRef mo = mkCUFConst(-1);
        PTRef fact = mkCUFTimes(mo, args[1]);
        args[1] = fact;
        return mkCUFPlus(args[0], args[1]);
    }
}

PTRef
CUFLogic::mkCUFPlus(const PTRef arg1, const PTRef arg2)
{
    PTRef tr = mkFun(sym_CUF_PLUS, {arg1, arg2});
    PTRef tr_comm = mkFun(sym_CUF_PLUS, {arg2, arg1});
    PTRef tr_comm_eq = mkEq(tr, tr_comm);
    if (!comm_eqs.has(tr_comm_eq))
        comm_eqs.insert(tr_comm_eq, true);
    return tr;
}

PTRef
CUFLogic::mkCUFTimes(const PTRef arg1, const PTRef arg2)
{
    PTRef tr = mkFun(sym_CUF_TIMES, {arg1, arg2});
    PTRef tr_comm = mkFun(sym_CUF_TIMES, {arg2, arg1});
    PTRef tr_comm_eq = mkEq(tr, tr_comm);
    if (!comm_eqs.has(tr_comm_eq))
        comm_eqs.insert(tr_comm_eq, true);
    return tr;
}

PTRef
CUFLogic::mkCUFDiv(const PTRef arg1, const PTRef arg2)
{
    PTRef tr = mkFun(sym_CUF_DIV, {arg1, arg2});
    return tr;
}

PTRef
CUFLogic::mkCUFGeq(const PTRef arg1, const PTRef arg2)
{
    return mkCUFLeq(arg2, arg1);
}

PTRef
CUFLogic::mkCUFLeq(const PTRef arg1, const PTRef arg2)
{
    if (isCUFNUMConst(arg1) && isCUFNUMConst(arg2)) {
        int c1 = getCUFNUMConst(arg1);
        int c2 = getCUFNUMConst(arg2);
        if (c1 <= c2)
            return getTerm_true();
        else
            return getTerm_false();
    }
    PTRef leq_tr = mkFun(sym_CUF_LEQ, {arg1, arg2});
    return mkOr(leq_tr, mkEq(arg1, arg2));
}

PTRef
CUFLogic::mkCUFGt(const PTRef arg1, const PTRef arg2)
{
    if (isCUFNUMConst(arg1) && isCUFNUMConst(arg2)) {
        int c1 = getCUFNUMConst(arg1);
        int c2 = getCUFNUMConst(arg2);
        if (c1 > c2)
            return getTerm_true();
        else
            return getTerm_false();
    }
    PTRef tr = mkFun(sym_CUF_GT, {arg1, arg2});
    // a>b -> a != b
    PTRef tr_eq = mkEq(arg1, arg2);
    PTRef n_tr_eq = mkCUFNot(tr_eq);
    PTRef tr_impl = mkImpl(n_tr_eq, n_tr_eq);
    if (!diseq_eqs.has(tr_impl))
        diseq_eqs.insert(tr_impl, true);
    return tr;
}

PTRef CUFLogic::mkCUFLt(const PTRef arg1, const PTRef arg2)
{
    return mkCUFGt(arg2, arg1);
}

PTRef CUFLogic::mkCUFLshift(const PTRef arg1, const PTRef arg2)
{
    if (isCUFNUMConst(arg2) && getCUFNUMConst(arg2) == 0)
        return arg1;
    return mkFun(sym_CUF_LSHIFT, {arg1, arg2});
}

PTRef CUFLogic::mkCUFLRshift(const PTRef arg1, const PTRef arg2)
{
    if (isCUFNUMConst(arg2) && getCUFNUMConst(arg2) == 0)
        return arg1;
    return mkFun(sym_CUF_LRSHIFT, {arg1, arg2});
}

PTRef CUFLogic::mkCUFARshift(const PTRef arg1, const PTRef arg2)
{
    if (isCUFNUMConst(arg2) && getCUFNUMConst(arg2) == 0)
        return arg1;
    return mkFun(sym_CUF_ARSHIFT, {arg1, arg2});
}

PTRef CUFLogic::mkCUFMod(const PTRef arg1, const PTRef arg2)
{
    if (isCUFNUMConst(arg2) && getCUFNUMConst(arg2) == 1)
        return getTerm_CUFZero();
    // if b > 0, then 0 <= a % b < b
    // if b < 0, then b < a % b <= 0
    return mkFun(sym_CUF_MOD, {arg1, arg2});
}

PTRef CUFLogic::mkCUFBwAnd(const PTRef arg1, const PTRef arg2)
{
    PTRef tr = mkFun(sym_CUF_BWAND, {arg1, arg2});
    PTRef tr_comm = mkFun(sym_CUF_BWAND, {arg2, arg1});
    PTRef tr_comm_eq = mkEq(tr, tr_comm);
    if (!comm_eqs.has(tr_comm_eq))
        comm_eqs.insert(tr_comm_eq, true);
    return tr;
}

PTRef CUFLogic::mkCUFBwOr(const PTRef arg1, const PTRef arg2)
{
    PTRef tr = mkFun(sym_CUF_BWOR, {arg1, arg2});
    PTRef tr_comm = mkFun(sym_CUF_BWOR, {arg2, arg1});
    PTRef tr_comm_eq = mkEq(tr, tr_comm);
    if (!comm_eqs.has(tr_comm_eq))
        comm_eqs.insert(tr_comm_eq, true);
    return tr;
}

PTRef CUFLogic::mkCUFInc(const PTRef arg1)
{
    PTRef tr = mkFun(sym_CUF_INC, {arg1});
    PTRef neq = mkCUFNeq(arg1, tr);
    if (!inc_diseqs.has(neq))
        inc_diseqs.insert(neq, true);
    return tr;
}

PTRef CUFLogic::mkCUFDec(const PTRef arg1)
{
    PTRef tr = mkFun(sym_CUF_DEC, {arg1});
    PTRef neq = mkCUFNeq(arg1, tr);
    if (!inc_diseqs.has(neq))
        inc_diseqs.insert(neq, true);
    return tr;
}

PTRef CUFLogic::mkCUFLand(const PTRef arg1, const PTRef arg2)
{
    PTRef tr = mkFun(sym_CUF_LAND, {arg1, arg2});
    return tr;
}

PTRef CUFLogic::mkCUFLor(const PTRef arg1, const PTRef arg2)
{
    PTRef tr = mkFun(sym_CUF_LOR, {arg1, arg2});
    return tr;
}

PTRef CUFLogic::mkCUFNot(const PTRef arg)
{
    return Logic::mkNot(arg);
}

PTRef CUFLogic::mkCUFBwXor(const PTRef arg1, const PTRef arg2)
{
    PTRef tr = mkFun(sym_CUF_BWXOR, {arg1, arg2});
    PTRef tr_comm = mkFun(sym_CUF_BWXOR, {arg2, arg1});
    PTRef tr_comm_eq = mkEq(tr, tr_comm);
    if (!comm_eqs.has(tr_comm_eq))
        comm_eqs.insert(tr_comm_eq, true);
    return tr;
}

PTRef CUFLogic::mkCUFCompl(const PTRef arg1)
{
    PTRef tr = mkFun(sym_CUF_COMPL, {arg1});
    PTRef neq = mkCUFNeq(tr, arg1);
    if (!compl_diseqs.has(neq))
        compl_diseqs.insert(neq, true);
    return tr;
}

PTRef CUFLogic::mkCUFSizeof(const PTRef arg)
{
    return mkFun(sym_CUF_SIZEOF, {arg});
}

PTRef CUFLogic::mkCUFAddrof(const PTRef arg)
{
    return mkFun(sym_CUF_SIZEOF, {arg});
}


PTRef CUFLogic::mkCUFPtr(const PTRef arg)
{
    return mkFun(sym_CUF_PTR, {arg});
}

PTRef CUFLogic::mkCUFCond(const PTRef cond, PTRef i_arg, PTRef e_arg)
{
    return mkIte(cond, i_arg, e_arg);
}

PTRef CUFLogic::mkCUFNeq(const PTRef a1, const PTRef a2)
{
    return Logic::mkNot(Logic::mkEq(a1, a2));
}

int CUFLogic::getCUFNUMConst(PTRef tr) const
{
    return atoi(getSymName(tr));
}

PTRef CUFLogic::conjoinExtras(PTRef root)
{
    PTRef root_out = root;
    root_out = mkAnd(root_out, mkAnd(comm_eqs.getKeys()));
    root_out = mkAnd(root_out, mkAnd(diseq_eqs.getKeys()));
    root_out = mkAnd(root_out, mkAnd(diseq_split.getKeys()));
    root_out = mkAnd(root_out, mkAnd(mod_ineqs.getKeys()));
    root_out = mkAnd(root_out, mkAnd(inc_diseqs.getKeys()));
    root_out = mkAnd(root_out, mkAnd(compl_diseqs.getKeys()));
    return root_out;
}
