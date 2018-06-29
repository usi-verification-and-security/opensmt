#ifndef LALOGIC_H
#define LALOGIC_H

#include "Logic.h"
#include "Real.h"

class LALogic: public Logic
{

    protected:

        Logic_t logic_type;

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

        bool split_eq;
        Map<PTRef,bool,PTRefHash> la_split_inequalities;

    public:
        LALogic(SMTConfig &c);
        ~LALogic() {}

        virtual bool    isBuiltinFunction(SymRef sr) const;
        virtual PTRef   insertTerm      (SymRef sym, vec<PTRef>& terms, char** msg);
        virtual SRef    getSort_num    ()              const { return sort_NUM; }

        //PS. be careful with the following, the main problem is with type opensmt:: Real, can i say either of the types? or how to say it? Line 58-60 has to be written properly and non of the methods needs to present in LRALogic.h file

        virtual PTRef       mkConst         (const char* name, const char **msg);
        //virtual PTRef       mkConst         (SRef s, const char* name);
       // virtual PTRef       mkConst         (const opensmt::Real& c) { char* rat; opensmt::stringToRational(rat, c.get_str().c_str()); PTRef tr = mkConst(getSort_num(), rat); free(rat); return tr; }
       // virtual PTRef       mkConst         (const char* num) { return mkConst(getSort_num(), num); }
       // virtual PTRef       mkRealVar       (const char* name) { return mkVar(getSort_num(), name); }

        virtual bool isBuiltinSort  (SRef sr) const { return sr == sort_NUM || Logic::isBuiltinSort(sr); }
        virtual bool isBuiltinConstant(SymRef sr) const { return (isNumConst(sr) || Logic::isBuiltinConstant(sr)); }


        virtual bool  isNumConst     (SymRef sr)     const { return isConstant(sr) && hasSortNum(sr); }
        virtual bool  isNumConst     (PTRef tr)      const { return isNumConst(getPterm(tr).symb()); }
        virtual bool  isNonnegNumConst (PTRef tr)    const; //{ return isNumConst(tr) && getNumConst(tr) >= 0; } //PS. will be done later

        virtual bool   hasSortNum(SymRef sr) const { return sym_store[sr].rsort() == sort_NUM; }
        virtual bool   hasSortNum(PTRef tr) const { return hasSortNum(getPterm(tr).symb()); }

        virtual const void* getNumConst(PTRef tr) const; //PS. how to be with the type here ??? the same correction do i LRALOgixc.h line 126

        virtual bool        isUFEquality(PTRef tr) const { return !isNumEq(tr) && Logic::isUFEquality(tr); }
        virtual bool        isTheoryEquality(PTRef tr) const { return isNumEq(tr); }

        virtual bool isAtom(PTRef tr) const  { return isNumEq(tr) || isNumLt(tr) || isNumGt(tr) || isNumLeq(tr) || isNumGeq(tr) || Logic::isAtom(tr); }

        virtual bool        isUF(PTRef tr) const { return isUF(term_store[tr].symb()); }
        virtual bool        isUF(SymRef sr) const { return !sym_store[sr].isInterpreted(); }
        //PS. up to here


                bool isNumPlus(SymRef sr) const { return sr == sym_Num_PLUS; }
        virtual bool isNumPlus(PTRef tr) const { return isNumPlus(getPterm(tr).symb()); }

                bool isNumMinus(SymRef sr) const { return sr == sym_Num_MINUS; }
        virtual bool isNumMinus(PTRef tr) const { return isNumMinus(getPterm(tr).symb()); }

                bool isNumNeg(SymRef sr) const { return sr == sym_Num_NEG; }
        virtual bool isNumNeg(PTRef tr) const { return isNumNeg(getPterm(tr).symb()); }

                bool isNumTimes(SymRef sr) const { return sr == sym_Num_TIMES; }
        virtual bool isNumTimes(PTRef tr) const { return isNumTimes(getPterm(tr).symb()); }

                bool isNumDiv(SymRef sr) const { return sr == sym_Num_DIV; }
        virtual bool isNumDiv(PTRef tr) const { return isNumDiv(getPterm(tr).symb()); }

                bool isNumEq(SymRef sr) const { return isEquality(sr) && (sym_store[sr][0] == sort_NUM);}
        virtual bool isNumEq(PTRef tr) const { return isNumEq(getPterm(tr).symb()); }

                bool isNumLeq(SymRef sr) const { return sr == sym_Num_LEQ; }
        virtual bool isNumLeq(PTRef tr) const { return isNumLeq(getPterm(tr).symb()); }

                bool isNumLt(SymRef sr) const { return sr == sym_Num_LT; }
        virtual bool isNumLt(PTRef tr) const { return isNumLt(getPterm(tr).symb()); }

                bool isNumGeq(SymRef sr) const { return sr == sym_Num_GEQ; }
        virtual bool isNumGeq(PTRef tr) const { return isNumGeq(getPterm(tr).symb()); }

                bool isNumGt(SymRef sr) const { return sr == sym_Num_GT; }
        virtual bool isNumGt(PTRef tr) const { return isNumGt(getPterm(tr).symb()); }

                bool isNumVar(SymRef sr) const { return isVar(sr) && sym_store[sr].rsort() == sort_NUM; }
        virtual bool isNumVar(PTRef tr) const { return isNumVar(getPterm(tr).symb()); }

                bool isNumZero(SymRef sr) const { return sr == sym_Num_ZERO; }
        virtual bool isNumZero(PTRef tr) const { return tr == term_Num_ZERO; }

                bool isNumOne(SymRef sr) const { return sr == sym_Num_ONE; }
        virtual bool isNumOne(PTRef tr) const { return tr == term_Num_ONE; }

        // Real terms are of form c, a, or (* c a) where c is a constant and
        // a is a variable.
        virtual bool isNumTerm(PTRef tr) const;
        virtual bool okForBoolVar(PTRef) const;

        virtual PTRef getNterm(char* rat_str) =0;

        virtual PTRef getTerm_NumZero() const { return term_Num_ZERO; }
        virtual PTRef getTerm_NumOne() const { return term_Num_ONE; }


        PTRef mkNumNeg(PTRef, char **);
        PTRef mkNumNeg(PTRef tr) {
            char *msg;
            PTRef trn = mkNumNeg(tr, &msg);
            assert(trn != PTRef_Undef);
            return trn;
        }

        PTRef mkNumMinus(const vec<PTRef> &, char **);
        PTRef mkNumMinus(const vec<PTRef> &args) {
            char *msg;
            PTRef tr = mkNumMinus(args, &msg);
            assert(tr != PTRef_Undef);
            return tr;
        }
        PTRef mkNumMinus(const PTRef a1, const PTRef a2) {
            vec<PTRef> tmp;
            tmp.push(a1);
            tmp.push(a2);
            return mkNumMinus(tmp);
        }

        PTRef mkNumPlus(const vec<PTRef> &, char **);
        PTRef mkNumPlus(const vec<PTRef> &args) {
            char *msg;
            PTRef tr = mkNumPlus(args, &msg);
            assert(tr != PTRef_Undef);
            return tr;
        }
        PTRef mkNumPlus(const std::vector<PTRef> &args) {
            vec<PTRef> tmp;
            for (PTRef arg : args) { tmp.push(arg); }
            return mkNumPlus(tmp);
        }

        PTRef mkNumTimes(const vec<PTRef> &, char **);
        PTRef mkNumTimes(const vec<PTRef> &args) {
            char *msg;
            PTRef tr = mkNumTimes(args, &msg);
            assert(tr != PTRef_Undef);
            return tr;
        }
        PTRef mkNumTimes(const PTRef p1, const PTRef p2) {
            vec<PTRef> tmp;
            tmp.push(p1);
            tmp.push(p2);
            return mkNumTimes(tmp);
        }
        PTRef mkNumTimes(const std::vector<PTRef> &args) {
            vec<PTRef> tmp;
            for (PTRef arg : args) { tmp.push(arg); }
            return mkNumTimes(tmp);
        }

        PTRef mkNumDiv(const vec<PTRef> &, char **);
        PTRef mkNumDiv(const vec<PTRef> &args) {
            char *msg;
            PTRef tr = mkNumDiv(args, &msg);
            assert(tr != PTRef_Undef);
            return tr;
        }
        PTRef mkNumDiv(const PTRef nom, const PTRef den) {
            vec<PTRef> tmp;
            tmp.push(nom), tmp.push(den);
            return mkNumDiv(tmp);
        }

        PTRef mkNumLeq(const vec<PTRef> &, char **);
        PTRef mkNumLeq(const vec<PTRef> &args) {
            char *msg;
            PTRef tr = mkNumLeq(args, &msg);
            assert(tr != PTRef_Undef);
            return tr;
        }
        PTRef mkNumLeq(const PTRef arg1, const PTRef arg2) {
            vec<PTRef> tmp;
            tmp.push(arg1);
            tmp.push(arg2);
            return mkNumLeq(tmp);
        }

        PTRef mkNumGeq(const vec<PTRef> &, char **);
        PTRef mkNumGeq(const vec<PTRef> &args) {
            char *msg;
            PTRef tr = mkNumGeq(args, &msg);
            assert(tr != PTRef_Undef);
            return tr;
        }
        PTRef mkNumGeq(const PTRef arg1, const PTRef arg2) {
            vec<PTRef> tmp;
            tmp.push(arg1);
            tmp.push(arg2);
            return mkNumGeq(tmp);
        }

        PTRef mkNumLt(const vec<PTRef> &, char **);
        PTRef mkNumLt(const vec<PTRef> &args) {
            char *msg;
            PTRef tr = mkNumLt(args, &msg);
            assert(tr != PTRef_Undef);
            return tr;
        }
        PTRef mkNumLt(const PTRef arg1, const PTRef arg2) {
            vec<PTRef> tmp;
            tmp.push(arg1);
            tmp.push(arg2);
            return mkNumLt(tmp);
        }

        PTRef mkNumGt(const vec<PTRef> &, char **);
        PTRef mkNumGt(const vec<PTRef> &args) {
            char *msg;
            PTRef tr = mkNumGt(args, &msg);
            assert(tr != PTRef_Undef);
            return tr;
        }
        PTRef mkNumGt(const PTRef arg1, const PTRef arg2) {
            vec<PTRef> tmp;
            tmp.push(arg1);
            tmp.push(arg2);
            return mkNumGt(tmp);
        }

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
        virtual char *printTerm(PTRef tr) const { return printTerm_(tr, false, false); }
        virtual char *printTerm(PTRef tr, bool l, bool s) const { return printTerm_(tr, l, s); }
        //up to here are methods that you can also find in Logic.h and Logic.C files

/*
    //delete all below
    virtual void
    SimplifyConst::simplify(SymRef &s, const vec<PTRef> &args, SymRef &s_new, vec<PTRef> &args_new, char **msg) {
        vec<int> const_idx;
        vec<PTRef> args_new_2;
        for (int i = 0; i < args.size(); i++) {
            if (l.isConstant(args[i]) || (l.isNumNeg(args[i]) && l.isConstant(l.getPterm(args[i])[0])))
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
        if (args_new.size() == 1 && (l.isNumPlus(s_new) || l.isNumTimes(s_new) || l.isNumDiv(s_new))) {
            PTRef ch_tr = args_new[0];
            args_new.clear();
            s_new = l.getPterm(ch_tr).symb();
            for (int i = 0; i < l.getPterm(ch_tr).size(); i++)
                args_new.push(l.getPterm(ch_tr)[i]);
        }
    }

    void SimplifyConstSum::constSimplify(const SymRef &s, const vec<PTRef> &terms, SymRef &s_new,
                                         vec<PTRef> &terms_new) const {
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

    virtual void SimplifyConstTimes::constSimplify(const SymRef &s, const vec<PTRef> &terms, SymRef &s_new,
                                                   vec<PTRef> &terms_new) const {
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
            if (!l.isNumOne(terms[i])) {
                if (l.isNumPlus(terms[i]))
                    plus = terms[i];
                else if (l.isConstant(terms[i]))
                    con = terms[i];
                else
                    terms_new.push(terms[i]);
            }
        }
        if (con == PTRef_Undef && plus == PTRef_Undef);
        else if (con == PTRef_Undef && plus != PTRef_Undef)
            terms_new.push(plus);
        else if (con != PTRef_Undef && plus == PTRef_Undef)
            terms_new.push(con);
        else {
            Pterm &p = l.getPterm(plus);
            vec<PTRef> sum_args;
            for (int i = 0; i < p.size(); ++i) {
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

    virtual void SimplifyConstDiv::constSimplify(const SymRef &s, const vec<PTRef> &terms, SymRef &s_new,
                                                 vec<PTRef> &terms_new) const {
        assert(terms_new.size() == 0);
        assert(terms.size() <= 2);
        if (terms.size() == 2 && l.isNumZero(terms[1])) {
            printf("Explicit div by zero\n");
            assert(false);
        }
        if (l.isNumOne(terms[terms.size() - 1])) {
            terms_new.clear();
            s_new = l.getPterm(terms[0]).symb();
            for (int i = 0; i < l.getPterm(terms[0]).size(); i++)
                terms_new.push(l.getPterm(terms[0])[i]);
            return;
        } else if (l.isNumZero(terms[0])) {
            terms_new.clear();
            s_new = l.getPterm(terms[0]).symb();
            return;
        }
        for (int i = 0; i < terms.size(); i++)
            terms_new.push(terms[i]);
        s_new = s;
    }

*/
};


// Determine for two multiplicative terms (* k1 v1) and (* k2 v2), v1 !=
// v2 which one is smaller, based on the PTRef of v1 and v2.  (i.e.
// v1.ptref <  v2.ptref iff (* k1 v1) < (* k2 v2))

//PS. how to access these classes from LIA and LRA? or not needed having them in LALogic class is enough?
// PS. what this means "but both logics could use LALessThan_deepPTRef directly."?
//PS. how to be with the functions we included in this file in the .C files of LIA and LRA? how call and use them?
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

//PS. can I write implementation of the following in above although class defined after };???
template <class Number = opensmt::Real>
class SimplifyConst {
  protected:
    LALogic& l;
    PTRef simplifyConstOp(const vec<PTRef>& const_terms, char** msg);
    virtual void Op(Number& s, const Number& v) const = 0; //PS. how to be with opensmt::Real?
    //virtual void Op(void* s, const void* v) const = 0;
    virtual Number getIdOp() const = 0;
    //virtual void* getIdOp() const = 0;
    virtual void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const = 0;
  public:
    SimplifyConst(LALogic& log) : l(log) {}
    void simplify(SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new, char** msg);
};

template <class Number = opensmt::Real>
class SimplifyConstSum : public SimplifyConst <Number>{
    void Op(Number& s, const Number& v) const { s += v; }
    //void Op(void* s, const void* v) const { s += v; }
    Number getIdOp() const { return 0; }
    //void* getIdOp() const { return 0; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
  public:
    SimplifyConstSum(LALogic& log) : SimplifyConst <Number> (log) {}
};

template <class Number = opensmt::Real>
class SimplifyConstTimes : public SimplifyConst <Number>{
    void Op(Number& s, const Number& v) const { s *= v; }
    //void Op(void* s, const void* v) const { s *= v; }
    Number getIdOp() const { return 1; }
    //void* getIdOp() const { return 1; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
  public:
    SimplifyConstTimes(LALogic& log) : SimplifyConst <Number> (log) {}
};

template <class Number = opensmt::Real>
class SimplifyConstDiv : public SimplifyConst <Number>{
    void Op(Number& s, const Number& v) const { if (v == 0) { printf("explicit div by zero\n"); } s /= v; }
    //void Op(void* s, const void* v) const { if (v == 0) { printf("explicit div by zero\n"); } s /= v; }
    Number getIdOp() const { return 1; }
    //void* getIdOp() const { return 1; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
  public:
    SimplifyConstDiv(LALogic& log) : SimplifyConst <Number> (log) {}
};


#endif
