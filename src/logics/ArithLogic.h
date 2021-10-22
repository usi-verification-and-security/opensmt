#ifndef LALOGIC_H
#define LALOGIC_H
#include "Logic.h"
#include "Number.h"
#include "OsmtInternalException.h"
#include <numeric>

class LANonLinearException : std::runtime_error
{
public:
    LANonLinearException(const char* reason_) : runtime_error(reason_) {
    }
    virtual const char* what() const noexcept
    {
        char* out;
        int chars_written = asprintf(&out, "Term %s is non-linear", std::runtime_error::what());
        assert(chars_written >= 0);
        (void) chars_written;
        return out;
    }
    ~LANonLinearException() = default;
};

class ArithDivisionByZeroException : public std::runtime_error
{
public:
    ArithDivisionByZeroException() : runtime_error("Explicit division by zero encountered!") {}
    ~ArithDivisionByZeroException() = default;
};

class ArithLogic: public Logic
{
    friend class LessThan_deepPTRef;
protected:
    std::vector<FastRational*> numbers;

    static const std::string e_nonlinear_term;

    static const std::string tk_val_int_default;
    static const std::string tk_val_real_default;
    static const std::string tk_real_zero;
    static const std::string tk_int_zero;
    static const std::string tk_real_one;
    static const std::string tk_int_one;
    static const std::string tk_real_neg;
    static const std::string tk_int_neg;
    static const std::string tk_real_minus;
    static const std::string tk_int_minus;
    static const std::string tk_real_plus;
    static const std::string tk_int_plus;
    static const std::string tk_real_times;
    static const std::string tk_int_times;
    static const std::string tk_real_ntimes;
    static const std::string tk_int_ntimes;
    static const std::string tk_real_div;
    static const std::string tk_real_ndiv;
    static const std::string tk_int_div;
    static const std::string tk_int_mod;
    static const std::string tk_real_leq;
    static const std::string tk_int_leq;
    static const std::string tk_real_lt;
    static const std::string tk_int_lt;
    static const std::string tk_real_geq;
    static const std::string tk_int_geq;
    static const std::string tk_real_gt;
    static const std::string tk_int_gt;
    static const std::string tk_real_abs;
    static const std::string tk_int_abs;
    static const std::string s_sort_real;
    static const std::string s_sort_int;

    // Reals
    SRef                sort_REAL;
    PTRef               term_Real_ZERO;
    PTRef               term_Real_ONE;
    PTRef               term_Real_MINUSONE;

    SymRef              sym_Real_ZERO;
    SymRef              sym_Real_ONE;
    SymRef              sym_Real_NEG;
    SymRef              sym_Real_MINUS;
    SymRef              sym_Real_ABS;
    SymRef              sym_Real_PLUS;
    SymRef              sym_Real_TIMES;
    SymRef              sym_Real_NTIMES;
    SymRef              sym_Real_DIV;
    SymRef              sym_Real_NDIV;
    SymRef              sym_Real_EQ;
    SymRef              sym_Real_LEQ;
    SymRef              sym_Real_LT;
    SymRef              sym_Real_GEQ;
    SymRef              sym_Real_GT;
    SymRef              sym_Real_ITE;


    // Integers
    SRef                sort_INT;
    PTRef               term_Int_ZERO;
    PTRef               term_Int_ONE;
    PTRef               term_Int_MINUSONE;
    SymRef              sym_Int_ZERO;
    SymRef              sym_Int_ONE;
    SymRef              sym_Int_NEG;
    SymRef              sym_Int_MINUS;
    SymRef              sym_Int_ABS;
    SymRef              sym_Int_PLUS;
    SymRef              sym_Int_TIMES;
    SymRef              sym_Int_NTIMES;
    SymRef              sym_Int_DIV;
    SymRef              sym_Int_NDIV;
    SymRef              sym_Int_MOD;
    SymRef              sym_Int_NMOD;
    SymRef              sym_Int_EQ;
    SymRef              sym_Int_LEQ;
    SymRef              sym_Int_LT;
    SymRef              sym_Int_GEQ;
    SymRef              sym_Int_GT;
    SymRef              sym_Int_ITE;

public:
    enum class ArithType {
        LIA, LRA, NIA, NRA, LIRA, NIRA, RDL, IDL
    };

private:
    ArithType           arithType;
    std::vector<std::string> const logicNames;
    vec<const opensmt::Logic_t> const logicTypes;
    vec<const SRef> const defaultSorts;

    SymRef get_sym_Num_PLUS() const;
    SymRef get_sym_Num_MINUS() const;
    SymRef get_sym_Num_TIMES() const;
    SymRef get_sym_Num_NTIMES() const;

public:
    ArithLogic(ArithType arithType);
    ~ArithLogic() { for (auto number : numbers) { delete number; } }
    const char       *getName() const override { return logicNames[static_cast<int>(arithType)].data(); }
    const opensmt::Logic_t getLogic() const override { return logicTypes[static_cast<int>(arithType)]; }
    bool             isBuiltinFunction(SymRef sr) const override;
    PTRef            insertTerm       (SymRef sym, vec<PTRef> && terms) override;
    const SRef       getSort_num      () const { return defaultSorts[static_cast<int>(arithType)]; }
    SRef             getSort_real     () const { return sort_REAL; }
    SRef             getSort_int      () const { return sort_INT; }
    PTRef            mkConst          (const char* name) override;
    PTRef            mkConst          (SRef s, const char* name) override;
    PTRef            mkConst          (SRef s, const std::string& name) { return mkConst(s, name.c_str()); }
    PTRef            mkConst          (const opensmt::Number& c);
    PTRef            mkNumVar         (const char* name) { return mkVar(getSort_num(), name); }
    PTRef            mkIntVar         (const char* name) { return mkVar(sort_INT, name); }
    PTRef            mkRealVar        (const char* name) { return mkVar(sort_REAL, name); }

    bool             isBuiltinSort    (SRef sr) const override { return sr == getSort_int() ||sr == getSort_real() || Logic::isBuiltinSort(sr); }
    bool             isBuiltinConstant(SymRef sr) const override { return (isIntConst(sr) || isRealConst(sr) || Logic::isBuiltinConstant(sr)); }

    bool isNumConst (SymRef sr) const { return Logic::isConstant(sr) && hasSortNum(sr); }
    bool isNumConst (PTRef tr)  const { return isNumConst(getPterm(tr).symb()); }
    bool isIntConst(SymRef sr) const { return isNumConst(sr) && (sym_store[sr].rsort() == getSort_int()); }
    bool isIntConst (PTRef tr) const { return isIntConst(getPterm(tr).symb()); }
    bool isRealConst(SymRef sr) const { return isNumConst(sr) && (sym_store[sr].rsort() == getSort_real()); }
    bool isRealConst (PTRef tr) const { return isRealConst(getPterm(tr).symb()); }

    bool isNonnegNumConst (PTRef tr) const { return isNumConst(tr) && getNumConst(tr) >= 0; }

    bool hasSortInt(SymRef sr) const { return sym_store[sr].rsort() == getSort_int(); }
    bool hasSortInt(PTRef tr)  const { return hasSortInt(getPterm(tr).symb()); }
    bool hasSortReal(SymRef sr) const { return sym_store[sr].rsort() == getSort_real(); }
    bool hasSortReal(PTRef tr)  const { return hasSortReal(getPterm(tr).symb()); }
    bool hasSortNum(SymRef sr) const { return hasSortInt(sr) || hasSortReal(sr); }
    bool hasSortNum(PTRef tr)  const { return hasSortInt(tr) || hasSortReal(tr); }

    const FastRational & getNumConst(PTRef tr) const;

    bool           isUFEquality(PTRef tr) const override { return !isNumEq(tr) && Logic::isUFEquality(tr); }
    bool           isTheoryEquality(PTRef tr) const override { return isNumEq(tr); }
    bool           isAtom(PTRef tr) const override { return isNumEq(tr) || isNumLt(tr) || isNumGt(tr) || isNumLeq(tr) || isNumGeq(tr) || Logic::isAtom(tr); }
    bool           isUF(PTRef tr) const override { return isUF(term_store[tr].symb()); }
    bool           isUF(SymRef sr) const override { return !sym_store[sr].isInterpreted(); }
    const char*    getDefaultValue(const PTRef tr) const override;
    PTRef          getDefaultValuePTRef(const SRef sref) const override;


    const SymRef get_sym_Int_TIMES () const { return sym_Int_TIMES; }
    const SymRef get_sym_Real_TIMES () const { return sym_Real_TIMES; }
    const SymRef get_sym_Int_NTIMES () const { return sym_Int_NTIMES; }
    const SymRef get_sym_Real_NTIMES () const { return sym_Real_NTIMES; }
    const SymRef get_sym_Int_DIV () const { return sym_Int_DIV; }
    const SymRef get_sym_Int_MOD () const { return sym_Int_MOD; }
    const SymRef get_sym_Int_NDIV () const { return sym_Int_NDIV; }
    const SymRef get_sym_Real_DIV () const { return sym_Real_DIV; }
    const SymRef get_sym_Real_NDIV () const { return sym_Real_NDIV; }
    const SymRef get_sym_Int_MINUS () const { return sym_Int_MINUS; }
    const SymRef get_sym_Real_MINUS () const { return sym_Real_MINUS; }
    const SymRef get_sym_Real_PLUS () const {return sym_Real_PLUS; }
    const SymRef get_sym_Int_PLUS () const {return sym_Int_PLUS; }
    const SymRef get_sym_Int_NEG () const { return sym_Int_NEG; }
    const SymRef get_sym_Num_NEG () const;
    const SymRef get_sym_Num_LEQ () const;
    const SymRef get_sym_Int_LEQ() const { return sym_Int_LEQ; }
    const SymRef get_sym_Real_LEQ() const { return sym_Real_LEQ; }
    const SymRef get_sym_Num_GEQ () const;
    const SymRef get_sym_Int_GEQ() const { return sym_Int_GEQ; }
    const SymRef get_sym_Real_GEQ() const { return sym_Real_GEQ; }
    const SymRef get_sym_Num_LT () const;
    const SymRef get_sym_Int_LT() const { return sym_Int_LT; }
    const SymRef get_sym_Real_LT() const { return sym_Real_LT; }
    const SymRef get_sym_Num_GT () const;
    const SymRef get_sym_Int_GT() const { return sym_Int_GT; }
    const SymRef get_sym_Real_GT() const { return sym_Real_GT; }
    const SymRef get_sym_Num_EQ () const;
    const SymRef get_sym_Int_EQ() const { return sym_Int_EQ; }
    const SymRef get_sym_Real_EQ() const { return sym_Real_EQ; }
    const SymRef get_sym_Num_ZERO () const;
    const SymRef get_Sym_Int_ZERO () const { return sym_Int_ZERO; }
    const SymRef get_Sym_Real_ZERO () const { return sym_Real_ZERO; }
    const SymRef get_sym_Num_ONE () const;
    const SymRef get_Sym_Int_ONE() const { return sym_Int_ONE; }
    const SymRef get_Sym_Real_ONE() const { return sym_Real_ONE; }
    const SymRef get_sym_Num_ITE () const;
    const SymRef get_sym_Int_ITE() const { return sym_Int_ITE;}
    const SymRef get_sym_Real_ITE() const { return sym_Real_ITE; }
    const SymRef get_sym_Num_ABS () const;
    const SymRef get_sym_Int_ABS() const { return sym_Int_ABS; }
    const SymRef get_sym_Real_ABS() const { return sym_Real_ABS; }


    bool isIntegralLogic() const;
    bool isRealLogic() const;

    const SRef get_sort_Num () const {
        if (not isIntegralLogic() and not isRealLogic()) {
            throw OsmtInternalException("Expected non-mixed logic");
        }
        return isIntegralLogic() ? sort_INT : sort_REAL; };

    void checkArithSortCompatibleAndDefined(PTRef tr) const;

    void checkArithSortCompatible(vec<PTRef> const & args, SRef numSort) const {
        for (auto tr : args) {
            if (getSortRef(tr) != numSort) throw OsmtApiException("Argument sorts disagree"); } }

    void checkArithSortCompatible(vec<PTRef> const & args) const {
        checkArithSortCompatible(args, getSortRef(args[0]));
    }
    void checkArithSortCompatibleAndDefined(vec<PTRef> const & args) const { checkArithSortDefined(); checkArithSortCompatible(args, get_sort_Num()); }
    void checkArithSortDefined() const { if (not isIntegralLogic() and not isRealLogic()) throw OsmtApiException("Arithmetic sort not uniquely defined"); }

    bool isNumPlus(SymRef sr) const { return sr == get_sym_Num_PLUS(); }
    bool isNumPlus(PTRef tr) const { return isNumPlus(getPterm(tr).symb()); }
    bool isIntPlus(SymRef sr) const { return sr == sym_Int_PLUS; }
    bool isIntPlus(PTRef tr) const { return isIntPlus(getPterm(tr).symb()); }
    bool isRealPlus(SymRef sr) const { return sr == sym_Real_PLUS; }
    bool isRealPlus(PTRef tr ) const { return isRealPlus(getPterm(tr).symb()); }

    bool isNumMinus(SymRef sr) const { return sr == get_sym_Num_MINUS(); }
    bool isIntMinus(SymRef sr) const { return sr == sym_Int_MINUS; }
    bool isIntMinus(PTRef tr) const { return isIntMinus(getPterm(tr).symb()); }
    bool isRealMinus(SymRef sr) const { return sr == sym_Real_MINUS; }
    bool isRealMinus(PTRef tr) const { return isRealMinus(getPterm(tr).symb()); }

    bool isNumNeg(SymRef sr) const { return sr == get_sym_Num_NEG(); }
    bool isNumNeg(PTRef tr) const { return isNumNeg(getPterm(tr).symb()); }
    bool isIntNeg(SymRef sr) const { return sr == sym_Int_NEG; }
    bool isIntNeg(PTRef tr) const { return isIntNeg(getPterm(tr).symb()); }
    bool isRealNeg(SymRef sr) const { return sr == sym_Real_NEG; }
    bool isRealNeg(PTRef tr) const { return isRealNeg(getPterm(tr).symb()); }

    bool isNumTimes(SymRef sr) const { return sr == get_sym_Num_TIMES(); }
    bool isNumTimes(PTRef tr) const { return isNumTimes(getPterm(tr).symb()); }
    bool isIntTimes(SymRef sr) const { return sr == get_sym_Int_TIMES(); }
    bool isIntTimes(PTRef tr) const { return isIntTimes(getPterm(tr).symb()); }
    bool isRealTimes(SymRef sr) const { return sr == get_sym_Real_TIMES(); }
    bool isRealTimes(PTRef tr) const { return isRealTimes(getPterm(tr).symb()); }

    bool isRealDiv(SymRef sr) const { return sr == get_sym_Real_DIV(); }
    bool isRealDiv(PTRef tr) const { return isRealDiv(getPterm(tr).symb()); }
    bool isIntDiv(SymRef sr) const { return sr == get_sym_Int_DIV(); }
    bool isIntDiv(PTRef tr) const { return isIntDiv(getPterm(tr).symb()); }
    bool isIntMod(SymRef sr)   const { return sr == sym_Int_MOD; }
    bool isIntAbs(SymRef sr)   const { return sr == sym_Int_ABS; }
    bool isIntAbs(PTRef tr) const { return isIntAbs(getPterm(tr).symb()); }
    bool isRealAbs(SymRef sr) const { return sr == sym_Real_ABS; }
    bool isRealAbs(PTRef tr) const { return isRealAbs(getPterm(tr).symb()); }
    bool isNumAbs(PTRef tr) const { return isIntAbs(tr) || isRealAbs(tr); }
    bool isNumAbs(SymRef sr) const { return isIntAbs(sr) || isRealAbs(sr); }

    bool isNumEq(SymRef sr) const { return isEquality(sr) && (sym_store[sr][0] == get_sort_Num());}
    bool isNumEq(PTRef tr) const { return isNumEq(getPterm(tr).symb()); }
    bool isIntEq(SymRef sr) const { return isEquality(sr) && sym_store[sr][0] == sort_INT; }
    bool isIntEq(PTRef tr) const { return isIntEq(getPterm(tr).symb()); }
    bool isRealEq(SymRef sr) const { return isEquality(sr) && sym_store[sr][0] == sort_REAL; }
    bool isRealEq(PTRef tr) const { return isIntEq(getPterm(tr).symb()); }

    bool isNumLeq(SymRef sr) const { return sr == get_sym_Num_LEQ(); }
    bool isNumLeq(PTRef tr) const { return isNumLeq(getPterm(tr).symb()); }
    bool isIntLeq(SymRef sr) const { return sr == sym_Int_LEQ; }
    bool isIntLeq(PTRef tr) const { return isIntLeq(getPterm(tr).symb()); }
    bool isRealLeq(SymRef sr) const { return sr == sym_Real_LEQ; }
    bool isRealLeq(PTRef tr) const { return isIntLeq(getPterm(tr).symb()); }

    bool isNumLt(SymRef sr) const { return sr == get_sym_Num_LT(); }
    bool isNumLt(PTRef tr) const { return isNumLt(getPterm(tr).symb()); }

    bool isNumGeq(SymRef sr) const { return sr == get_sym_Num_GEQ(); }
    bool isNumGeq(PTRef tr) const { return isNumGeq(getPterm(tr).symb()); }
    bool isNumGt(SymRef sr) const { return sr == get_sym_Num_GT(); }
    bool isNumGt(PTRef tr) const { return isNumGt(getPterm(tr).symb()); }
    bool isNumVar(SymRef sr) const { return isVar(sr) && sym_store[sr].rsort() == get_sort_Num(); }
    bool isNumVar(PTRef tr) const { return isNumVar(getPterm(tr).symb()); }
    bool isNumVarOrIte(SymRef sr) const { return isNumVar(sr) || isIte(sr); }
    bool isNumVarOrIte(PTRef tr) const { return isNumVarOrIte(getPterm(tr).symb()); }
    bool isNumVarLike(SymRef tr) const { return isNumVarOrIte(tr) || isIntDiv(tr) || isIntMod(tr); }
    bool isNumVarLike(PTRef tr) const { return isNumVarLike(getPterm(tr).symb()); }
    bool isNumZero(SymRef sr) const { return sr == get_sym_Num_ZERO(); }
    bool isNumZero(PTRef tr) const { return tr == getTerm_NumZero(); }
    bool isNumOne(SymRef sr) const { return sr == get_sym_Num_ONE(); }
    bool isNumOne(PTRef tr) const { return tr == getTerm_NumOne(); }

    // Real terms are of form c, a, or (* c a) where c is a constant and a is a variable or Ite.
    virtual bool isNumTerm(PTRef tr) const;

    PTRef getTerm_NumZero()     const { checkArithSortDefined(); return isIntegralLogic() ? term_Int_ZERO : term_Real_ZERO; };
    PTRef getTerm_NumOne()      const { checkArithSortDefined(); return isIntegralLogic() ? term_Int_ONE : term_Real_ONE; };
    PTRef getTerm_NumMinusOne() const { checkArithSortDefined(); return isIntegralLogic() ? term_Int_MINUSONE : term_Real_MINUSONE; };

    PTRef getTerm_IntZero()     const { return term_Int_ZERO; };
    PTRef getTerm_IntOne()      const { return term_Int_ONE; };
    PTRef getTerm_IntMinusOne() const { return term_Int_MINUSONE; };

    PTRef getTerm_RealZero()     const { return term_Real_ZERO; };
    PTRef getTerm_RealOne()      const { return term_Real_ONE; };
    PTRef getTerm_RealMinusOne() const { return term_Real_MINUSONE; };

    void checkSortInt(PTRef tr) { if (getSortRef(tr) != getSort_int()) throw OsmtApiException("Expected integral sort"); }
    void checkSortReal(PTRef tr) { if (getSortRef(tr) != getSort_real()) throw OsmtApiException("Expected real sort"); }
    void checkSortInt(vec<PTRef> const & args) { if (args.size() > 0) checkSortInt(args[0]); }
    void checkSortReal(vec<PTRef> const & args) { if (args.size() > 0) checkSortReal(args[0]); }

    // Negation
    PTRef mkNumNeg(PTRef tr);
    PTRef mkIntNeg(PTRef tr) { checkSortInt(tr); return mkNumNeg(tr); }
    PTRef mkRealNeg(PTRef tr) { checkSortReal(tr); return mkNumNeg(tr); }

    // Minus
    PTRef mkNumMinus(vec<PTRef> &&);
    PTRef mkNumMinus(PTRef a1, PTRef a2) { return mkNumMinus(vec<PTRef>({a1, a2})); }
    PTRef mkNumMinus(vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkNumMinus(std::move(tmp)); }

    PTRef mkIntMinus(vec<PTRef> && args) { checkSortInt(args); return mkNumMinus(std::move(args)); }
    PTRef mkIntMinus(PTRef a1, PTRef a2) { return mkIntMinus(vec<PTRef>({a1, a2})); }
    PTRef mkIntMinus(vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkIntMinus(std::move(tmp)); }

    PTRef mkRealMinus(vec<PTRef> && args) { checkSortReal(args); return mkNumMinus(std::move(args)); }
    PTRef mkRealMinus(PTRef a1, PTRef a2) { return mkRealMinus(vec<PTRef>({a1, a2})); }
    PTRef mkRealMinus(vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkRealMinus(std::move(tmp)); }

    // Plus
    PTRef mkNumPlus(vec<PTRef> &&);
    PTRef mkNumPlus(PTRef p1, PTRef p2) { return mkNumPlus(vec<PTRef>({p1, p2})); }
    PTRef mkNumPlus(vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkNumPlus(std::move(tmp)); }
    PTRef mkNumPlus(std::vector<PTRef> const & args) { return mkNumPlus(vec<PTRef>(args)); }

    PTRef mkIntPlus(vec<PTRef> && args) { checkSortInt(args); return mkNumPlus(std::move(args)); }
    PTRef mkIntPlus(PTRef p1, PTRef p2) { return mkIntPlus(vec<PTRef>{p1, p2}); }
    PTRef mkIntPlus(vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkIntPlus(std::move(tmp)); }
    PTRef mkIntPlus(std::vector<PTRef> const & args) { return mkIntPlus(vec<PTRef>(args)); }

    PTRef mkRealPlus(vec<PTRef> && args) { checkSortReal(args); return mkNumPlus(std::move(args)); }
    PTRef mkRealPlus(PTRef p1, PTRef p2) { return mkRealPlus(vec<PTRef>{p1, p2}); }
    PTRef mkRealPlus(vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkNumPlus(std::move(tmp)); }
    PTRef mkRealPlus(std::vector<PTRef> const & args) { return mkRealPlus(vec<PTRef>(args)); }

    // Times
    PTRef mkNumTimes(vec<PTRef> && args);
    PTRef mkNumTimes(PTRef p1, PTRef p2) { return mkNumTimes(vec<PTRef>{p1, p2}); }
    PTRef mkNumTimes(vec<PTRef> const &args) { vec<PTRef> tmp; args.copyTo(tmp); return mkNumTimes(std::move(tmp)); }
    PTRef mkNumTimes(std::vector<PTRef> const &args) { return mkNumTimes(vec<PTRef>(args)); }

    PTRef mkIntTimes(vec<PTRef> && args) { checkSortInt(args); return mkNumTimes(std::move(args)); }
    PTRef mkIntTimes(PTRef p1, PTRef p2) { return mkIntTimes(vec<PTRef>{p1, p2}); }
    PTRef mkIntTimes(vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkIntTimes(std::move(tmp)); }
    PTRef mkIntTimes(std::vector<PTRef> const &args) { return mkIntTimes(vec<PTRef>(args)); }

    PTRef mkRealTimes(vec<PTRef> && args) { checkSortReal(args); return mkNumTimes(std::move(args)); }
    PTRef mkRealTimes(PTRef p1, PTRef p2) { return mkRealTimes(vec<PTRef>{p1, p2}); }
    PTRef mkRealTimes(vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkNumTimes(std::move(tmp)); }
    PTRef mkRealTimes(std::vector<PTRef> const &args) { return mkRealTimes(vec<PTRef>(args)); }

    // Div
    PTRef mkIntDiv(vec<PTRef> && args);
    PTRef mkIntDiv(PTRef nom, PTRef den) { return mkIntDiv(vec<PTRef>{nom, den}); }
    PTRef mkIntDiv(vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkIntDiv(std::move(tmp)); }

    PTRef mkRealDiv(vec<PTRef> && args);
    PTRef mkRealDiv(PTRef nom, PTRef den) { return mkRealDiv(vec<PTRef>{nom, den}); }
    PTRef mkRealDiv(vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkRealDiv(std::move(tmp)); }

    // Mod
    PTRef mkIntMod(vec<PTRef> && args);
    PTRef mkIntMod(PTRef first, PTRef second) { return mkIntMod(vec<PTRef>{first, second}); }

    // Abs
    PTRef mkNumAbs(PTRef p);
    PTRef mkIntAbs(PTRef p) { checkSortInt(p); return mkNumAbs(p); }
    PTRef mkRealAbs(PTRef p) { checkSortReal(p); return mkNumAbs(p); }

    // Leq
    PTRef mkNumLeq(vec<PTRef> const & args);
    PTRef mkNumLeq(PTRef arg1, PTRef arg2) { return mkBinaryLeq(arg1, arg2); }

    PTRef mkIntLeq(vec<PTRef> const & args) { checkSortInt(args); return mkNumLeq(args); };
    PTRef mkIntLeq(PTRef arg1, PTRef arg2) { checkSortInt(arg1); checkSortInt(arg2); return mkBinaryLeq(arg1, arg2); }

    PTRef mkRealLeq(vec<PTRef> const & args) { checkSortReal(args); return mkNumLeq(args); };
    PTRef mkRealLeq(PTRef arg1, PTRef arg2) { checkSortReal(arg1); checkSortReal(arg2); return mkBinaryLeq(arg1, arg2); }

    // Geq
    PTRef mkNumGeq(vec<PTRef> const & args);
    PTRef mkNumGeq(PTRef arg1, PTRef arg2) { return mkBinaryGeq(arg1, arg2); }

    PTRef mkIntGeq(vec<PTRef> const & args) { checkSortInt(args); return mkNumGeq(args); }
    PTRef mkIntGeq(PTRef arg1, PTRef arg2) { checkSortInt(arg1); checkSortInt(arg2); return mkBinaryGeq(arg1, arg2); }

    PTRef mkRealGeq(vec<PTRef> const & args) { checkSortReal(args); return mkNumGeq(args); }
    PTRef mkRealGeq(PTRef arg1, PTRef arg2) { checkSortReal(arg1); checkSortReal(arg2); return mkBinaryGeq(arg1, arg2); }

    // Lt
    PTRef mkNumLt(vec<PTRef> const & args);
    PTRef mkNumLt(PTRef arg1, PTRef arg2) { return mkBinaryLt(arg1, arg2); }

    PTRef mkIntLt(vec<PTRef> const & args) { checkSortInt(args); return mkNumLt(args); }
    PTRef mkIntLt(PTRef arg1, PTRef arg2) { checkSortInt(arg1); checkSortInt(arg2); return mkBinaryLt(arg1, arg2); }

    PTRef mkRealLt(vec<PTRef> const & args) { checkSortReal(args); return mkNumLt(args); }
    PTRef mkRealLt(PTRef arg1, PTRef arg2) { checkSortReal(arg1); checkSortReal(arg2); return mkBinaryLt(arg1, arg2); }

    // Gt
    PTRef mkNumGt(vec<PTRef> const & args);
    PTRef mkNumGt(PTRef arg1, PTRef arg2) { return mkBinaryGt(arg1, arg2); }

    PTRef mkIntGt(vec<PTRef> const & args) { checkSortInt(args); return mkNumGt(args); }
    PTRef mkIntGt(PTRef arg1, PTRef arg2) { checkSortInt(arg1); checkSortInt(arg2); return mkBinaryGt(arg1, arg2); }

    PTRef mkRealGt(vec<PTRef> const & args) { checkSortReal(args); return mkNumGt(args); }
    PTRef mkRealGt(PTRef arg1, PTRef arg2) { checkSortReal(arg1); checkSortReal(arg2); return mkBinaryGt(arg1, arg2); }

    virtual bool isNegated(PTRef tr) const;
    virtual bool isLinearTerm(PTRef tr) const;
    virtual bool isLinearFactor(PTRef tr) const;
    std::pair<opensmt::Number, vec<PTRef>> getConstantAndFactors(PTRef sum) const;
    virtual void splitTermToVarAndConst(PTRef term, PTRef &var, PTRef &fac) const;
    virtual PTRef normalizeMul(PTRef mul);
    // Given a sum term 't' returns a normalized inequality 'c <= s' equivalent to '0 <= t'
    PTRef intSumToNormalizedInequality(PTRef sum);
    PTRef realSumToNormalizedInequality(PTRef sum);
    PTRef sumToNormalizedInequality(PTRef sum);

    PTRef sumToNormalizedEquality(PTRef sum);
    PTRef intSumToNormalizedEquality(PTRef sum);
    PTRef realSumToNormalizedEquality(PTRef sum);
    virtual lbool arithmeticElimination(vec<PTRef> const & top_level_arith, SubstMap & substitutions);

    opensmt::pair<lbool,SubstMap> retrieveSubstitutions(vec<PtAsgn> const & facts) override;
    void termSort(vec<PTRef> &v) const override;
    char *printTerm_(PTRef tr, bool ext, bool s) const override;
    char *printTerm(PTRef tr) const override;
    char *printTerm(PTRef tr, bool l, bool s) const override;

    // Helper methods

    // Given an inequality 'c <= t', return the constant c; checked version
    PTRef getConstantFromLeq(PTRef);
    // Given an inequality 'c <= t', return the term t; checked version
    PTRef getTermFromLeq(PTRef);
    // Given an inequality 'c <= t', return the pair <c,t> for a constant c and term t; unchecked version, for internal use
    std::pair<PTRef, PTRef> leqToConstantAndTerm(PTRef);

    // MB: In pure LA, there are never nested boolean terms
    vec<PTRef> getNestedBoolRoots (PTRef)  const override { return vec<PTRef>(); }

protected:
    PTRef mkBinaryLeq(PTRef lhs, PTRef rhs);
    PTRef mkBinaryGeq(PTRef lhs, PTRef rhs);
    PTRef mkBinaryLt(PTRef lhs, PTRef rhs);
    PTRef mkBinaryGt(PTRef lhs, PTRef rhs);
    PTRef mkBinaryEq(PTRef lhs, PTRef rhs) override;
    opensmt::pair<FastRational, PTRef> sumToNormalizedPair(PTRef sum);
    opensmt::pair<FastRational, PTRef> sumToNormalizedIntPair(PTRef sum);
    opensmt::pair<FastRational, PTRef> sumToNormalizedRealPair(PTRef sum);
};

// Determine for two multiplicative terms (* k1 v1) and (* k2 v2), v1 !=
// v2 which one is smaller, based on the PTRef of v1 and v2.  (i.e.
// v1.ptref <  v2.ptref iff (* k1 v1) < (* k2 v2)).
//
// This code is required for canonicalising the terms and correctly identifying their sign.
//
// If term contains a const-ite:
//   (* ite v) or (* ite c) or (* v ite) or (* c ite)  => consider {v,c}.ptref
//   (* ite1 ite2) => consider min(ite1.ptref, ite2.ptref)
class LessThan_deepPTRef {
    const ArithLogic& l;
    uint32_t getVarIdFromProduct(PTRef term) const;
public:
    LessThan_deepPTRef(const ArithLogic* l) : l(*l) {}

    bool operator ()  (PTRef x_, PTRef y_) const;

};

class SimplifyConst {
protected:
    ArithLogic& l;
    PTRef simplifyConstOp(const vec<PTRef> & const_terms);
    virtual void Op(opensmt::Number& s, const opensmt::Number& v) const = 0;
    virtual opensmt::Number getIdOp() const = 0;
    virtual void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const = 0;
public:
    SimplifyConst(ArithLogic& log) : l(log) {}
    void simplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new);
};

class SimplifyConstSum : public SimplifyConst {
    void Op(opensmt::Number& s, const opensmt::Number& v) const;// { s += v; }
    opensmt::Number getIdOp() const;// { return 0; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
public:
    SimplifyConstSum(ArithLogic& log) : SimplifyConst(log) {}
};

class SimplifyConstTimes : public SimplifyConst {
    void Op(opensmt::Number& s, const opensmt::Number& v) const;// { s *= v; }
    opensmt::Number getIdOp() const;// { return 1; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
public:
    SimplifyConstTimes(ArithLogic& log) : SimplifyConst(log) {}
};

class SimplifyConstDiv : public SimplifyConst {
    void Op(opensmt::Number& s, const opensmt::Number& v) const;// { if (v == 0) { printf("explicit div by zero\n"); } s /= v; }
    opensmt::Number getIdOp() const;// { return 1; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
public:
    SimplifyConstDiv(ArithLogic& log) : SimplifyConst(log) {}
};
#endif