#ifndef LALOGIC_H
#define LALOGIC_H

#include "Logic.h"
#include "Number.h"

class LANonLinearException
{
    char* reason;
public:
    LANonLinearException(const char* reason_) {
        asprintf(&reason, "Term %s is non-linear", reason_);
    }
    virtual char* what() const
    {
        char* out;
        asprintf(&out, "%s", reason);
        return out;
    }
    ~LANonLinearException() { free(reason); }
};


class LALogic: public Logic
{

protected:

    Logic_t logic_type;
    vec<opensmt::Number*> numbers;
    SymRef sym_Num_ZERO;
    SymRef sym_Num_ONE;
    SymRef sym_Num_NEG;
    SymRef sym_Num_MINUS;
    SymRef sym_Num_PLUS;
    SymRef sym_Num_TIMES;
    SymRef sym_Num_DIV;
    SymRef sym_Num_EQ;
    SymRef sym_Num_LEQ;
    SymRef sym_Num_LT;
    SymRef sym_Num_GEQ;
    SymRef sym_Num_GT;
    SymRef sym_Num_ITE;


    PTRef term_Num_ZERO;
    PTRef term_Num_ONE;

    SRef      sort_NUM;

    bool split_eq;

    static const char*  tk_val_num_default;

    static const char *tk_num_zero;
    static const char *tk_num_one;
    static const char *tk_num_neg;
    static const char *tk_num_minus;
    static const char *tk_num_plus;
    static const char *tk_num_times;
    static const char *tk_num_div;
    static const char *tk_num_leq;
    static const char *tk_num_lt;
    static const char *tk_num_geq;
    static const char *tk_num_gt;

    static const char*  s_sort_num;


    Map<PTRef,bool,PTRefHash> la_split_inequalities;

public:
    LALogic(SMTConfig &c);
    ~LALogic() {}

    virtual bool    isBuiltinFunction(SymRef sr) const;
    virtual PTRef   insertTerm      (SymRef sym, vec<PTRef>& terms, char** msg);
    virtual SRef    getSort_num    ()              const; // { return sort_NUM; }

    //PS. be careful with the following, the main problem is with type opensmt:: Real, which in LIA needs to be opensmt:: Integer

    virtual PTRef     mkConst         (const char* name, const char **msg);
    virtual PTRef     mkConst         (SRef s, const char* name);
    virtual PTRef     mkConst         (const opensmt::Number& c); // { char* rat; opensmt::stringToRational(rat, c.get_str().c_str()); PTRef tr = mkConst(getSort_num(), rat); free(rat); return tr; }
    virtual PTRef     mkConst         (const char* num); // { return mkConst(getSort_num(), num); }
    virtual PTRef     mkNumVar        (const char* name); // { return mkVar(getSort_num(), name); }

    virtual bool isBuiltinSort  (SRef sr) const; // { return sr == sort_NUM || Logic::isBuiltinSort(sr); }
    virtual bool isBuiltinConstant(SymRef sr) const; // { return (isNumConst(sr) || Logic::isBuiltinConstant(sr)); }


    virtual bool  isNumConst     (SymRef sr)     const; // { return isConstant(sr) && hasSortNum(sr); }
    virtual bool  isNumConst     (PTRef tr)      const; // { return isNumConst(getPterm(tr).symb()); }
   // virtual bool  isNonnegNumConst (PTRef tr)    const; //{ return isNumConst(tr) && getNumConst(tr) >= 0; } //PS. this method will be rewritten properly later
    virtual bool  isNonnegNumConst (PTRef tr)  const; // { return isNumConst(tr) && getNumConst(tr) >= 0; }

    virtual bool   hasSortNum(SymRef sr) const; // { return sym_store[sr].rsort() == sort_NUM; }
    virtual bool   hasSortNum(PTRef tr)  const; // { return hasSortNum(getPterm(tr).symb()); }

    virtual const opensmt::Number& getNumConst(PTRef tr) const; //PS. this method will be rewritten properly later

    virtual bool        isUFEquality(PTRef tr) const; // { return !isNumEq(tr) && Logic::isUFEquality(tr); }
    virtual bool        isTheoryEquality(PTRef tr) const; // { return isNumEq(tr); }

    virtual bool isAtom(PTRef tr) const; //  { return isNumEq(tr) || isNumLt(tr) || isNumGt(tr) || isNumLeq(tr) || isNumGeq(tr) || Logic::isAtom(tr); }

    virtual bool        isUF(PTRef tr) const; // { return isUF(term_store[tr].symb()); }
    virtual bool        isUF(SymRef sr) const; // { return !sym_store[sr].isInterpreted(); }

    virtual const char* getDefaultValue(const PTRef tr) const;
    //PS. up to here


    virtual bool isNumPlus(SymRef sr) const; // { return sr == sym_Num_PLUS; }
    virtual bool isNumPlus(PTRef tr) const; // { return isNumPlus(getPterm(tr).symb()); }

    virtual bool isNumMinus(SymRef sr) const; // { return sr == sym_Num_MINUS; }
    virtual bool isNumMinus(PTRef tr) const ; //{ return isNumMinus(getPterm(tr).symb()); }

    virtual bool isNumNeg(SymRef sr) const ; //{ return sr == sym_Num_NEG; }
    virtual bool isNumNeg(PTRef tr) const ; // { return isNumNeg(getPterm(tr).symb()); }

    virtual bool isNumTimes(SymRef sr) const; // { return sr == sym_Num_TIMES; }
    virtual bool isNumTimes(PTRef tr) const ; //{ return isNumTimes(getPterm(tr).symb()); }

    virtual bool isNumDiv(SymRef sr) const; // { return sr == sym_Num_DIV; }
    virtual bool isNumDiv(PTRef tr) const; // { return isNumDiv(getPterm(tr).symb()); }

    virtual bool isNumEq(SymRef sr) const ; //{ return isEquality(sr) && (sym_store[sr][0] == sort_NUM);}
    virtual bool isNumEq(PTRef tr) const ; //{ return isNumEq(getPterm(tr).symb()); }

    virtual bool isNumLeq(SymRef sr) const; // { return sr == sym_Num_LEQ; }
    virtual bool isNumLeq(PTRef tr) const ; //{ return isNumLeq(getPterm(tr).symb()); }

    virtual  bool isNumLt(SymRef sr) const; // { return sr == sym_Num_LT; }
    virtual bool isNumLt(PTRef tr) const; // { return isNumLt(getPterm(tr).symb()); }

    virtual bool isNumGeq(SymRef sr) const; // { return sr == sym_Num_GEQ; }
    virtual bool isNumGeq(PTRef tr) const; // { return isNumGeq(getPterm(tr).symb()); }

    virtual bool isNumGt(SymRef sr) const ; //{ return sr == sym_Num_GT; }
    virtual bool isNumGt(PTRef tr) const; // { return isNumGt(getPterm(tr).symb()); }

    virtual bool isNumVar(SymRef sr) const; // { return isVar(sr) && sym_store[sr].rsort() == sort_NUM; }
    virtual bool isNumVar(PTRef tr) const; // { return isNumVar(getPterm(tr).symb()); }

    virtual bool isNumZero(SymRef sr) const; // { return sr == sym_Num_ZERO; }
    virtual bool isNumZero(PTRef tr) const; // { return tr == term_Num_ZERO; }

    virtual  bool isNumOne(SymRef sr) const; // { return sr == sym_Num_ONE; }
    virtual bool isNumOne(PTRef tr) const; // { return tr == term_Num_ONE; }

    // Real terms are of form c, a, or (* c a) where c is a constant and a is a variable.
    virtual bool isNumTerm(PTRef tr) const;
    virtual bool okForBoolVar(PTRef) const;

    //virtual PTRef getNTerm(char* rat_str) =0;

    virtual PTRef getTerm_NumZero() const; // { return term_Num_ZERO; }
    virtual PTRef getTerm_NumOne() const; // { return term_Num_ONE; }


    virtual PTRef mkNumNeg(PTRef, char **);
    virtual PTRef mkNumNeg(PTRef tr); // { char *msg; PTRef trn = mkNumNeg(tr, &msg); assert(trn != PTRef_Undef); return trn;}

    virtual PTRef mkNumMinus(const vec<PTRef> &, char **);
    virtual PTRef mkNumMinus(const vec<PTRef> &args); // { char *msg; PTRef tr = mkNumMinus(args, &msg); assert(tr != PTRef_Undef); return tr; }
    virtual  PTRef mkNumMinus(const PTRef a1, const PTRef a2); // { vec<PTRef> tmp; tmp.push(a1); tmp.push(a2); return mkNumMinus(tmp); }

    virtual PTRef mkNumPlus(const vec<PTRef> &, char **);
    virtual PTRef mkNumPlus(const vec<PTRef> &args); // { char *msg; PTRef tr = mkNumPlus(args, &msg); assert(tr != PTRef_Undef); return tr; }
    virtual  PTRef mkNumPlus(const std::vector<PTRef> &args); // { vec<PTRef> tmp; for (PTRef arg : args) { tmp.push(arg); } return mkNumPlus(tmp); }

    virtual PTRef mkNumTimes(const vec<PTRef> &, char **);
    virtual PTRef mkNumTimes(const vec<PTRef> &args); // { char *msg; PTRef tr = mkNumTimes(args, &msg); assert(tr != PTRef_Undef); return tr; }
    virtual  PTRef mkNumTimes(const PTRef p1, const PTRef p2); // { vec<PTRef> tmp; tmp.push(p1); tmp.push(p2); return mkNumTimes(tmp); }
    virtual  PTRef mkNumTimes(const std::vector<PTRef> &args); // { vec<PTRef> tmp; for (PTRef arg : args) { tmp.push(arg); } return mkNumTimes(tmp); }

    virtual PTRef mkNumDiv(const vec<PTRef> &, char **);
    virtual  PTRef mkNumDiv(const vec<PTRef> &args); // { char *msg; PTRef tr = mkNumDiv(args, &msg); assert(tr != PTRef_Undef); return tr; }
    virtual  PTRef mkNumDiv(const PTRef nom, const PTRef den); // { vec<PTRef> tmp; tmp.push(nom), tmp.push(den); return mkNumDiv(tmp); }

    virtual PTRef mkNumLeq(const vec<PTRef> &, char **);
    virtual PTRef mkNumLeq(const vec<PTRef> &args); // { char *msg; PTRef tr = mkNumLeq(args, &msg); assert(tr != PTRef_Undef); return tr; }
    virtual PTRef mkNumLeq(const PTRef arg1, const PTRef arg2); // {vec<PTRef> tmp; tmp.push(arg1); tmp.push(arg2); return mkNumLeq(tmp); }

    virtual PTRef mkNumGeq(const vec<PTRef> &, char **);
    virtual PTRef mkNumGeq(const vec<PTRef> &args); // { char *msg; PTRef tr = mkNumGeq(args, &msg); assert(tr != PTRef_Undef); return tr; }
    virtual PTRef mkNumGeq(const PTRef arg1, const PTRef arg2); // { vec<PTRef> tmp; tmp.push(arg1); tmp.push(arg2); return mkNumGeq(tmp); }

    virtual  PTRef mkNumLt(const vec<PTRef> &, char **);
    virtual PTRef mkNumLt(const vec<PTRef> &args); // { char *msg; PTRef tr = mkNumLt(args, &msg); assert(tr != PTRef_Undef); return tr; }
    virtual  PTRef mkNumLt(const PTRef arg1, const PTRef arg2); // { vec<PTRef> tmp; tmp.push(arg1); tmp.push(arg2); return mkNumLt(tmp); }

    virtual PTRef mkNumGt(const vec<PTRef> &, char **);
    virtual PTRef mkNumGt(const vec<PTRef> &args); // { char *msg; PTRef tr = mkNumGt(args, &msg); assert(tr != PTRef_Undef); return tr; }
    virtual PTRef mkNumGt(const PTRef arg1, const PTRef arg2); // { vec<PTRef> tmp; tmp.push(arg1); tmp.push(arg2); return mkNumGt(tmp); }

    //from here
    virtual bool isNegated(PTRef tr) const;
    virtual void splitTermToVarAndConst(const PTRef &term, PTRef &var, PTRef &fac) const;

    virtual PTRef normalizeSum(PTRef sum); // Use for normalizing leq terms: sort the sum and divide all terms with the first factor
    virtual PTRef normalizeMul(PTRef mul);

    virtual lbool arithmeticElimination(vec<PTRef> &, Map<PTRef, PtAsgn, PTRefHash> &);
    virtual void simplifyAndSplitEq(PTRef, PTRef &);
    //up to here are methods specific for LRA

    //from here
    virtual void visit(PTRef, Map<PTRef, PTRef, PTRefHash> &);
    virtual lbool retrieveSubstitutions(vec<PtAsgn> &facts, Map<PTRef, PtAsgn, PTRefHash> &substs);
    virtual void termSort(vec<PTRef> &v) const;
    virtual bool okToPartition(PTRef tr) const; // Partitioning hints from logic

    virtual void serializeLogicData(int *&logicdata_buf) const;
    virtual void deserializeLogicData(const int *logicdata_buf);

    virtual char *printTerm_(PTRef tr, bool ext, bool s) const;
    virtual char *printTerm(PTRef tr) const; // { return printTerm_(tr, false, false); }
    virtual char *printTerm(PTRef tr, bool l, bool s) const; // { return printTerm_(tr, l, s); }
    //up to here are methods that you can also find in Logic class

};


// Determine for two multiplicative terms (* k1 v1) and (* k2 v2), v1 !=
// v2 which one is smaller, based on the PTRef of v1 and v2.  (i.e.
// v1.ptref <  v2.ptref iff (* k1 v1) < (* k2 v2))


class LessThan_deepPTRef {
    const LALogic& l;
public:
    LessThan_deepPTRef(const LALogic* l) : l(*l) {}
    bool operator ()  (PTRef& x_, PTRef& y_) {
        uint32_t id_x;
        uint32_t id_y;
        if (l.isNumTimes(x_)) {
            PTRef c_x;
            PTRef v_x;
            l.splitTermToVarAndConst(x_, v_x, c_x);
            id_x = v_x.x;
        } else {
            id_x = x_.x;
        }
        if (l.isNumTimes(y_)) {
            PTRef c_y;
            PTRef v_y;
            l.splitTermToVarAndConst(y_, v_y, c_y);
            id_y = v_y.x;
        } else {
            id_y = y_.x;
        }
        return id_x < id_y;
    }
};


class SimplifyConst {
protected:
    LALogic& l;
    PTRef simplifyConstOp(const vec<PTRef>& const_terms, char** msg);
    virtual void Op(opensmt::Number& s, const opensmt::Number& v) const = 0; //PS. instead of opensmt:: REal we write Number
    virtual opensmt::Number getIdOp() const = 0;
    virtual void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const = 0;
public:
    SimplifyConst(LALogic& log) : l(log) {}
    void simplify(SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new, char** msg);
};

class SimplifyConstSum : public SimplifyConst{
    void Op(opensmt::Number& s, const opensmt::Number& v) const;// { s += v; }
    opensmt::Number getIdOp() const;// { return 0; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
public:
    SimplifyConstSum(LALogic& log) : SimplifyConst(log) {}
};

class SimplifyConstTimes : public SimplifyConst{
    void Op(opensmt::Number& s, const opensmt::Number& v) const;// { s *= v; }
    opensmt::Number getIdOp() const;// { return 1; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
public:
    SimplifyConstTimes(LALogic& log) : SimplifyConst(log) {}
};

class SimplifyConstDiv : public SimplifyConst{
    void Op(opensmt::Number& s, const opensmt::Number& v) const;// { if (v == 0) { printf("explicit div by zero\n"); } s /= v; }
    opensmt::Number getIdOp() const;// { return 1; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
public:
    SimplifyConstDiv(LALogic& log) : SimplifyConst(log) {}
};


#endif
