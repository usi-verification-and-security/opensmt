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
    ~LALogic() { for(int i = 0; i < numbers.size(); ++i) {delete numbers[i];}}
    virtual bool    isBuiltinFunction(SymRef sr) const override;
    virtual PTRef   insertTerm      (SymRef sym, vec<PTRef>& terms, char** msg) override;
    virtual SRef    getSort_num    ()              const;
    virtual PTRef     mkConst         (const char* name, const char **msg) override;
    virtual PTRef     mkConst         (SRef s, const char* name) override;
    virtual PTRef     mkConst         (const opensmt::Number& c);
    virtual PTRef     mkConst         (const char* num);
    virtual PTRef     mkNumVar        (const char* name);
    virtual bool isBuiltinSort  (SRef sr) const override;
    virtual bool isBuiltinConstant(SymRef sr) const override;
    virtual bool  isNumConst     (SymRef sr)     const;
    virtual bool  isNumConst     (PTRef tr)      const;
    virtual bool  isNonnegNumConst (PTRef tr)  const;
    virtual bool   hasSortNum(SymRef sr) const;
    virtual bool   hasSortNum(PTRef tr)  const;
    virtual const opensmt::Number& getNumConst(PTRef tr) const;
    virtual bool        isUFEquality(PTRef tr) const override;
    virtual bool        isTheoryEquality(PTRef tr) const override;
    virtual bool isAtom(PTRef tr) const override;
    virtual bool        isUF(PTRef tr) const override;
    virtual bool        isUF(SymRef sr) const override;
    virtual const char* getDefaultValue(const PTRef tr) const override;

    virtual const SymRef get_sym_Num_TIMES () const =0;
    virtual const SymRef get_sym_Num_DIV () const =0;
    virtual const SymRef get_sym_Num_MINUS () const =0;
    virtual const SymRef get_sym_Num_PLUS () const =0;
    virtual const SymRef get_sym_Num_NEG () const =0;
    virtual const SymRef get_sym_Num_LEQ () const =0;
    virtual const SymRef get_sym_Num_GEQ () const =0;
    virtual const SymRef get_sym_Num_LT () const =0;
    virtual const SymRef get_sym_Num_GT () const =0;
    virtual const SymRef get_sym_Num_EQ () const =0;
    virtual const SymRef get_sym_Num_ZERO () const =0;
    virtual const SymRef get_sym_Num_ONE () const =0;
    virtual const SymRef get_sym_Num_ITE () const =0;
    virtual const SRef get_sort_NUM () const =0;

    bool isNumPlus(SymRef sr) const;
    virtual bool isNumPlus(PTRef tr) const;
    bool isNumMinus(SymRef sr) const;
    virtual bool isNumMinus(PTRef tr) const ;
    bool isNumNeg(SymRef sr) const ;
    virtual bool isNumNeg(PTRef tr) const ;
    bool isNumTimes(SymRef sr) const;
    virtual bool isNumTimes(PTRef tr) const ;
    bool isNumDiv(SymRef sr) const;
    virtual bool isNumDiv(PTRef tr) const;
    bool isNumEq(SymRef sr) const ;
    virtual bool isNumEq(PTRef tr) const ;
    bool isNumLeq(SymRef sr) const;
    virtual bool isNumLeq(PTRef tr) const ;
    bool isNumLt(SymRef sr) const;
    virtual bool isNumLt(PTRef tr) const;
    bool isNumGeq(SymRef sr) const;
    virtual bool isNumGeq(PTRef tr) const;
    bool isNumGt(SymRef sr) const ;
    virtual bool isNumGt(PTRef tr) const;
    bool isNumVar(SymRef sr) const;
    virtual bool isNumVar(PTRef tr) const;
    bool isNumZero(SymRef sr) const;
    virtual bool isNumZero(PTRef tr) const;
    bool isNumOne(SymRef sr) const;
    virtual bool isNumOne(PTRef tr) const;
    // Real terms are of form c, a, or (* c a) where c is a constant and a is a variable.
    virtual bool isNumTerm(PTRef tr) const;
    virtual bool okForBoolVar(PTRef) const override;

    virtual PTRef getTerm_NumZero() const =0;
    virtual PTRef getTerm_NumOne() const =0;
    virtual PTRef mkNumNeg(PTRef, char **);
    virtual PTRef mkNumNeg(PTRef tr);
    virtual PTRef mkNumMinus(const vec<PTRef> &, char **);
    virtual PTRef mkNumMinus(const vec<PTRef> &args);
    virtual  PTRef mkNumMinus(const PTRef a1, const PTRef a2);
    virtual PTRef mkNumPlus(const vec<PTRef> &, char **);
    virtual PTRef mkNumPlus(const vec<PTRef> &args);
    virtual  PTRef mkNumPlus(const std::vector<PTRef> &args);
    virtual PTRef mkNumTimes(const vec<PTRef> &, char **);
    virtual PTRef mkNumTimes(const vec<PTRef> &args);
    virtual  PTRef mkNumTimes(const PTRef p1, const PTRef p2);
    virtual  PTRef mkNumTimes(const std::vector<PTRef> &args);
    virtual PTRef mkNumDiv(const vec<PTRef> &, char **);
    virtual  PTRef mkNumDiv(const vec<PTRef> &args);
    virtual  PTRef mkNumDiv(const PTRef nom, const PTRef den);
    virtual PTRef mkNumLeq(const vec<PTRef> &, char **);
    virtual PTRef mkNumLeq(const vec<PTRef> &args);
    virtual PTRef mkNumLeq(const PTRef arg1, const PTRef arg2);
    virtual PTRef mkNumGeq(const vec<PTRef> &, char **);
    virtual PTRef mkNumGeq(const vec<PTRef> &args);
    virtual PTRef mkNumGeq(const PTRef arg1, const PTRef arg2);
    virtual  PTRef mkNumLt(const vec<PTRef> &, char **);
    virtual PTRef mkNumLt(const vec<PTRef> &args);
    virtual  PTRef mkNumLt(const PTRef arg1, const PTRef arg2);
    virtual PTRef mkNumGt(const vec<PTRef> &, char **);
    virtual PTRef mkNumGt(const vec<PTRef> &args);
    virtual PTRef mkNumGt(const PTRef arg1, const PTRef arg2);

    virtual bool isNegated(PTRef tr) const;
    virtual void splitTermToVarAndConst(const PTRef &term, PTRef &var, PTRef &fac) const;
    virtual PTRef normalizeSum(PTRef sum);
    virtual PTRef normalizeMul(PTRef mul);
    virtual lbool arithmeticElimination(const vec<PTRef> & top_level_arith,
                                        Map<PTRef, PtAsgn, PTRefHash> & substitutions);
    virtual void simplifyAndSplitEq(PTRef, PTRef &);

    virtual void visit(PTRef, Map<PTRef, PTRef, PTRefHash> &) override;
    virtual lbool retrieveSubstitutions(const vec<PtAsgn> &facts, Map<PTRef, PtAsgn, PTRefHash> &substs) override;
    virtual void termSort(vec<PTRef> &v) const override;
    virtual bool okToPartition(PTRef tr) const override; // Partitioning hints from logic
    virtual void serializeLogicData(int *&logicdata_buf) const override;
    virtual void deserializeLogicData(const int *logicdata_buf) override;
    virtual char *printTerm_(PTRef tr, bool ext, bool s) const override;
    virtual char *printTerm(PTRef tr) const override;
    virtual char *printTerm(PTRef tr, bool l, bool s) const override;

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
    PTRef simplifyConstOp(const vec<PTRef> & const_terms);
    virtual void Op(opensmt::Number& s, const opensmt::Number& v) const = 0;
    virtual opensmt::Number getIdOp() const = 0;
    virtual void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const = 0;
public:
    SimplifyConst(LALogic& log) : l(log) {}
    void simplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new, char** msg);
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