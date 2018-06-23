#ifndef LALOGIC_H
#define LALOGIC_H

class LALogic {
  protected:
    Logic_t logic_type;

    SymRef              sym_Num_ZERO;
    SymRef              sym_Num_ONE;
    SymRef              sym_Num_NEG;
    SymRef              sym_Num_MINUS;
    SymRef              sym_Num_PLUS;
    SymRef              sym_Num_TIMES;
    SymRef              sym_Num_DIV;
    SymRef              sym_Num_EQ;
    SymRef              sym_Num_LEQ;
    SymRef              sym_Num_LT;
    SymRef              sym_Num_GEQ;
    SymRef              sym_Num_GT;
    SymRef              sym_Num_ITE;

    //SRef                sort_REAL //PS. what type should I have here for later use? Maybe sort_MIXED this anyway declaration of variable of type SRef

    PTRef               term_Num_ZERO;
    PTRef               term_Num_ONE;

    static const char*  tk_num_zero;
    static const char*  tk_num_one;
    static const char*  tk_num_neg;
    static const char*  tk_num_minus;
    static const char*  tk_num_plus;
    static const char*  tk_num_times;
    static const char*  tk_num_div;
    static const char*  tk_num_leq;
    static const char*  tk_num_lt;
    static const char*  tk_num_geq;
    static const char*  tk_num_gt;

    bool split_eq;

  public:
    LALogic                    (SMTConfig& c);
    ~LALogic                   () {}

    bool        isNumPlus(SymRef sr) const { return sr == sym_Num_PLUS; }
    virtual bool        isNumPlus(PTRef tr) const { return isNumPlus(getPterm(tr).symb()); }
    bool        isNumMinus(SymRef sr) const { return sr == sym_Num_MINUS; }
    virtual bool        isNumMinus(PTRef tr) const { return isNumMinus(getPterm(tr).symb()); }
    bool        isNumNeg(SymRef sr) const { return sr == sym_Num_NEG; }
    virtual bool        isNumNeg(PTRef tr) const { return isNumNeg(getPterm(tr).symb()); }
    bool        isNumTimes(SymRef sr) const { return sr == sym_Num_TIMES; }
    virtual bool        isNumTimes(PTRef tr) const { return isNumTimes(getPterm(tr).symb()); }
    bool        isNumDiv(SymRef sr) const { return sr == sym_Num_DIV; }
    virtual bool        isNumDiv(PTRef tr) const { return isNumDiv(getPterm(tr).symb()); }
    bool        isNumEq(SymRef sr) const { return isEquality(sr) && (sym_store[sr][0] == sort_BOOL); } //what sort to write here?
    virtual bool        isNumEq(PTRef tr) const { return isNumEq(getPterm(tr).symb()); }
    bool        isNumLeq(SymRef sr) const { return sr == sym_Num_LEQ; }
    virtual bool        isNumLeq(PTRef tr) const { return isNumLeq(getPterm(tr).symb()); }
    bool        isNumLt(SymRef sr) const { return sr == sym_Num_LT; }
    virtual bool        isNumLt(PTRef tr) const { return isNumLt(getPterm(tr).symb()); }
    bool        isNumGeq(SymRef sr) const { return sr == sym_Num_GEQ; }
    virtual bool        isNumGeq(PTRef tr) const { return isNumGeq(getPterm(tr).symb()); }
    bool        isNumGt(SymRef sr) const { return sr == sym_Num_GT; }
    virtual bool        isNumGt(PTRef tr) const { return isNumGt(getPterm(tr).symb()); }
    bool        isNumVar(SymRef sr) const { return isVar(sr) && sym_store[sr].rsort() == sort_BOOL; } //??
    virtual bool        isNumVar(PTRef tr) const { return isNumVar(getPterm(tr).symb()); }
    bool        isNumZero(SymRef sr) const { return sr == sym_Num_ZERO; }
    virtual bool        isNumZero(PTRef tr) const { return tr == term_Num_ZERO; }
    bool        isNumOne(SymRef sr) const { return sr == sym_Num_ONE; }
    virtual bool        isNumOne(PTRef tr) const { return tr == term_Num_ONE; }

    // Real terms are of form c, a, or (* c a) where c is a constant and
    // a is a variable.
    bool        isNumTerm(PTRef tr) const;

    //PS. the rest also needs to be overriden, but how?

    PTRef       getTerm_NumZero() const { return term_Num_ZERO; }
    PTRef       getTerm_NumOne()  const { return term_Num_ONE; }
    PTRef       mkNumNeg(PTRef, char**);
    PTRef       mkNumNeg(PTRef tr) {char* msg; PTRef trn = mkNumNeg(tr, &msg); assert(trn != PTRef_Undef); return trn; }
    PTRef       mkNumMinus(const vec<PTRef>&, char**);
    PTRef       mkNumMinus(const vec<PTRef>& args) { char *msg; PTRef tr = mkNumMinus(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkNumMinus(const PTRef a1, const PTRef a2) { vec<PTRef> tmp; tmp.push(a1); tmp.push(a2); return mkNumMinus(tmp); }
    PTRef       mkNumPlus(const vec<PTRef>&, char**);
    PTRef       mkNumPlus(const vec<PTRef>& args) { char *msg; PTRef tr = mkNumPlus(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkNumPlus(const std::vector<PTRef>& args) { vec<PTRef> tmp; for(PTRef arg : args) {tmp.push(arg);} return mkNumPlus(tmp);}
    PTRef       mkNumTimes(const vec<PTRef>&, char**);
    PTRef       mkNumTimes(const vec<PTRef>& args) { char *msg; PTRef tr = mkNumTimes(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkNumTimes(const PTRef p1, const PTRef p2) { vec<PTRef> tmp; tmp.push(p1); tmp.push(p2); return mkNumTimes(tmp); }
    PTRef       mkNumTimes(const std::vector<PTRef>& args) { vec<PTRef> tmp; for(PTRef arg : args) {tmp.push(arg);} return mkNumTimes(tmp);}
    PTRef       mkNumDiv(const vec<PTRef>&, char**);
    PTRef       mkNumDiv(const vec<PTRef>& args) { char *msg; PTRef tr = mkNumDiv(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkNumDiv(const PTRef nom, const PTRef den) { vec<PTRef> tmp; tmp.push(nom), tmp.push(den); return mkNumDiv(tmp); }
    PTRef       mkNumLeq(const vec<PTRef>&, char**);
    PTRef       mkNumLeq(const vec<PTRef>& args) { char* msg; PTRef tr = mkNumLeq(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkNumLeq(const PTRef arg1, const PTRef arg2) { vec<PTRef> tmp; tmp.push(arg1); tmp.push(arg2); return mkNumLeq(tmp); }
    PTRef       mkNumGeq(const vec<PTRef>&, char**);
    PTRef       mkNumGeq(const vec<PTRef>& args) { char* msg; PTRef tr = mkNumGeq(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkNumGeq(const PTRef arg1, const PTRef arg2) { vec<PTRef> tmp; tmp.push(arg1); tmp.push(arg2); return mkNumGeq(tmp); }
    PTRef       mkNumLt(const vec<PTRef>&, char**);
    PTRef       mkNumLt(const vec<PTRef>& args) { char* msg; PTRef tr = mkNumLt(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkNumLt(const PTRef arg1, const PTRef arg2) { vec<PTRef> tmp; tmp.push(arg1); tmp.push(arg2); return mkNumLt(tmp); }
    PTRef       mkNumGt(const vec<PTRef>&, char**);
    PTRef       mkNumGt(const vec<PTRef>& args) { char* msg; PTRef tr = mkNumGt(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkNumGt(const PTRef arg1, const PTRef arg2) { vec<PTRef> tmp; tmp.push(arg1); tmp.push(arg2); return mkNumGt(tmp); }

    //bool        isNegated(PTRef tr) const;

    virtual bool isNegated(PTRef tr) const {
      if (isNumConst(tr))
          return getNumConst(tr) < 0; // Case (0a) and (0b) //PS. getNumConst needs to be overriden for LIA and LRA
      if (isNumVar(tr))
          return false; // Case (1a)
      if (isNumTimes(tr)) {
          // Cases (2)
          PTRef v;
          PTRef c;
          splitTermToVarAndConst(tr, v, c); //PS. splitTermToVarAndConst needs to be in this classs defined and implemented
          return isNegated(c);
      }
      else {
          // Cases(3)
          return isNegated(getPterm(tr)[0]);
      }
    }


    //void        splitTermToVarAndConst(const PTRef& term, PTRef& var, PTRef& fac) const;

    //PS. be careful with below function implementation as it contains DIV, for LIA you may need to activate it, or rewrite new implementation for LIA

    virtual void splitTermToVarAndConst(const PTRef& term, PTRef& var, PTRef& fac) const {
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
          fac = getTerm_RealOne();
      } else {
          var = getTerm_RealOne();
          fac = term;
      }
    }

    //PTRef       normalizeSum(PTRef sum); // Use for normalizing leq terms: sort the sum and divide all terms with the first factor

    virtual PTRef normalizeSum(PTRef sum) {
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
      opensmt::Real k = abs(isConstant(t[0]) ? getNumConst(t[0]) : getNumConst(t[1])); //PS. how to be with opensmt: Real? in case of integer? override method and reimplement?
      PTRef divisor = mkConst(k); //PS. how this implementation will differentiate between mkConst of LRA and LIA? And how at all say in this base class that mkConst is from where? logic.h?
      for (int i = 0; i < args.size(); i++) {
          vec<PTRef> tmp;
          tmp.push(args[i]);
          tmp.push(divisor);
          args[i] = mkNumDiv(tmp);
      }
      return mkNumPlus(args);
    }


    //PTRef       normalizeMul(PTRef mul); // Use for normalizing leq terms of form 0 <= c*v

    virtual PTRef  normalizeMul(PTRef mul)
    {
        assert(isNumTimes(mul));
        PTRef v = PTRef_Undef;
        PTRef c = PTRef_Undef;
        splitTermToVarAndConst(mul, v, c);
        opensmt::Real r = getNumConst(c);
        if (r < 0)
            return mkNumNeg(v); //PS. how to override mk methods?
        else
            return v;
    }

    // Logic specific simplifications: conjoin Ites, make substitutions
    // and split equalities

    //lbool arithmeticElimination(vec<PTRef>&, Map<PTRef,PtAsgn,PTRefHash>&);


    virtual lbool arithmeticElimination(vec<PTRef> &top_level_arith, Map<PTRef,PtAsgn,PTRefHash>& substitutions)
    {
        vec<LAExpression*> equalities; //PS. u need to change somethin inside LAExpression
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

    //void simplifyAndSplitEq(PTRef, PTRef&);

    virtual void simplifyAndSplitEq(PTRef tr, PTRef& root_out)
    {
        split_eq = true;
        simplifyTree(tr, root_out);
        split_eq = false;
    }

    virtual void termSort(vec<PTRef>& v) const;
    virtual bool okToPartition(PTRef tr) const; // Partitioning hints from logic
    virtual void serializeLogicData(int*& logicdata_buf) const;
    void deserializeLogicData(const int* logicdata_buf);

    virtual char* printTerm_       (PTRef tr, bool ext, bool s) const;
    virtual char* printTerm        (PTRef tr)                 const { return printTerm_(tr, false, false); }
    virtual char* printTerm        (PTRef tr, bool l, bool s) const { return printTerm_(tr, l, s); }
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


class SimplifyConst {
  protected:
    LALogic& l;
    PTRef simplifyConstOp(const vec<PTRef>& const_terms, char** msg);
    virtual void Op(opensmt::Real& s, const opensmt::Real& v) const = 0; //PS. how to be with opensmt::Real?
    virtual opensmt::Real getIdOp() const = 0;
    virtual void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const = 0;
  public:
    SimplifyConst(LALogic& log) : l(log) {}
    void simplify(SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new, char** msg);
};

class SimplifyConstSum : public SimplifyConst {
    void Op(opensmt::Real& s, const opensmt::Real& v) const { s += v; }
    opensmt::Real getIdOp() const { return 0; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
  public:
    SimplifyConstSum(LALogic& log) : SimplifyConst(log) {}
};

class SimplifyConstTimes : public SimplifyConst {
    void Op(opensmt::Real& s, const opensmt::Real& v) const { s *= v; }
    opensmt::Real getIdOp() const { return 1; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
  public:
    SimplifyConstTimes(LALogic& log) : SimplifyConst(log) {}
};

class SimplifyConstDiv : public SimplifyConst {
    void Op(opensmt::Real& s, const opensmt::Real& v) const { if (v == 0) { printf("explicit div by zero\n"); } s /= v; }
    opensmt::Real getIdOp() const { return 1; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
  public:
    SimplifyConstDiv(LALogic& log) : SimplifyConst(log) {}
};


#endif
