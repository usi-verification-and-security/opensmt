//include all necessary header files
//in LALogic.h file make all methods shared by other virtual


bool LALogic::isNegated(PTRef tr) const {
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
        var = getTerm_NumOne();
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
    opensmt::Real k = abs(isConstant(t[0]) ? getNumConst(t[0]) : getNumConst(t[1]));
    PTRef divisor = mkConst(k);
    for (int i = 0; i < args.size(); i++) {
        vec<PTRef> tmp;
        tmp.push(args[i]);
        tmp.push(divisor);
        args[i] = mkNumDiv(tmp);
    }
    return mkNumPlus(args);
}

// Normalize a product of the form (* a v) to either v or (* -1 v)
PTRef LALogic::normalizeMul(PTRef mul)
{
    assert(isNumTimes(mul));
    PTRef v = PTRef_Undef;
    PTRef c = PTRef_Undef;
    splitTermToVarAndConst(mul, v, c);
    opensmt::Real r = getNumConst(c);
    if (r < 0)
        return mkNumNeg(v);
    else
        return v;
}

//PS. do we at all need this method for LIA

lbool LALogic::arithmeticElimination(vec<PTRef> &top_level_arith, Map<PTRef,PtAsgn,PTRefHash>& substitutions)
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


lbool LALogic::retrieveSubstitutions(vec<PtAsgn>& facts, Map<PTRef,PtAsgn,PTRefHash>& substs)
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

void LALogic::serializeLogicData(int*& logicdata_buf) const
{
    Logic::serializeLogicData(logicdata_buf);
    vec<SymRef> real_syms;
    for (int i = 0; i < reals.size(); i++)
        if (reals[i] != NULL)
            real_syms.push(sym_store.symbols[i]);

#ifdef VERBOSE_FOPS
    printf("Found %d real symbols\n", real_syms.size());
#endif
    int size_old = logicdata_buf[buf_sz_idx];
    int size_new = size_old + real_syms.size() + 2;
    logicdata_buf = (int*) realloc(logicdata_buf, size_new*sizeof(int));
    logicdata_buf[size_old] = real_syms.size();
    for (int i = 0; i < real_syms.size(); i++)
        logicdata_buf[size_old+1+i] = real_syms[i].x;
    logicdata_buf[buf_sz_idx] = size_new;
}

void LALogic::deserializeLogicData(const int* logicdata_buf)
{
    Logic::deserializeLogicData(logicdata_buf);
    int mydata_init = logicdata_buf[constants_offs_idx] + logicdata_buf[logicdata_buf[constants_offs_idx]];
    assert(mydata_init < logicdata_buf[0]); // Inside the buffer still
    int sz = logicdata_buf[mydata_init];
    for (int i = 0; i < sz; i++) {
        SymRef sr = {(uint32_t) logicdata_buf[mydata_init+1+i]};
        SymId id = sym_store[sr].getId();
        for (int j = reals.size(); j <= id; j++)
            reals.push(NULL);
        reals[id] = new opensmt::Real(sym_store.idToName[id]);
        while (id >= constants.size())
            constants.push(false);
        constants[id] = true;
    }
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
#ifdef PRODUCE_PROOF
        ipartitions_t &part = getIPartitions(tr);
        addIPartitions(i1, part);
        addIPartitions(i2, part);
#endif
        args.clear();
        args.push(i1); args.push(i2);
        PTRef andr = mkAnd(args);
        la_split_inequalities.insert(i1, true);
        la_split_inequalities.insert(i2, true);
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

bool LALogic::isBuiltinFunction(const SymRef sr) const
{
    if (sr == sym_Num_NEG || sr == sym_Num_MINUS || sr == sym_Num_PLUS || sr == sym_Num_TIMES || sr == sym_Num_DIV || sr == sym_Num_EQ || sr == sym_Num_LEQ || sr == sym_Num_LT || sr == sym_Num_GEQ || sr == sym_Num_GT || sr == sym_Num_ITE) return true;
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

bool
LALogic::okForBoolVar(PTRef tr) const
{
    return isNumLeq(tr) || Logic::okForBoolVar(tr);
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
        char* rat_str;
        opensmt::stringToRational(rat_str, sym_store.getName(getPterm(tr).symb()));
        opensmt::Real v(rat_str);
        free(rat_str);
        v = -v;
        PTRef nterm = mkConst(getSort_real(), v.get_str().c_str());
        SymRef s = getPterm(nterm).symb();
        return mkFun(s, args, msg);
    }
    PTRef mo = mkConst(getSort_real(), "-1");
    args.push(mo); args.push(tr);
    return mkNumTimes(args);
}

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
    PTRef mo = mkConst(getSort_real(), "-1");
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
    vec<PTRef> tmp_args;
    new_args.copyTo(tmp_args);
    //for (int i = 0; i < new_args.size(); i++)
    //    args.push(new_args[i]);

    SimplifyConstSum simp(*this);
    vec<PTRef> args_new;
    SymRef s_new;
    simp.simplify(sym_Num_PLUS, tmp_args, s_new, args_new, msg);
    if (args_new.size() == 1)
        return args_new[0];


    // This code takes polynomials (+ (* v c1) (* v c2)) and converts them to the form (* v c3) where c3 = c1+c2
    VecMap<PTRef,PTRef,PTRefHash> s2t;
    vec<PTRef> keys;
    for (int i = 0; i < args_new.size(); ++i) {
        PTRef v;
        PTRef c;
        splitTermToVarAndConst(args_new[i], v, c);
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
        vec<PTRef>& consts = s2t[keys[i]];
        PTRef consts_summed = mkNumPlus(consts);
        vec<PTRef> term_args;
        term_args.push(consts_summed);
        if (keys[i] != PTRef_Undef)
            term_args.push(keys[i]);
        else term_args.push(getTerm_NumOne());
        PTRef term = mkNumTimes(term_args);
        if (!isNumZero(term))
            sum_args.push(term);
    }

    if (sum_args.size() == 1) return sum_args[0];
    PTRef tr = mkFun(s_new, sum_args, msg);
//    PTRef tr = mkFun(s_new, args_new, msg);
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
    simp.simplify(sym_Num_TIMES, args, s_new, args_new, msg);
    PTRef tr = mkFun(s_new, args_new, msg);
    // Either a real term or, if we constructed a multiplication of a
    // constant and a sum, a real sum.
    if (isNumTerm(tr) || isNumPlus(tr) || isUF(tr))
        return tr;
    else {
        char* err;
        asprintf(&err, "%s", printTerm(tr));
        throw LANonLinearException(err);
    }
}

//PS. this method and alike you should make virtual and in LRA and LIA classes override approprietly
PTRef LALogic::mkNumDiv(const vec<PTRef>& args, char** msg)
{
    SimplifyConstDiv simp(*this);
    vec<PTRef> args_new;
    SymRef s_new;

    simp.simplify(sym_Num_DIV, args, s_new, args_new, msg);
    assert(args.size() == 2);

    if (isNumDiv(s_new)) {
        assert(isNumTerm(args_new[0]) && isConstant(args_new[1]));
        args_new[1] = mkConst(FastRational_inverse(getNumConst(args_new[1]))); //mkConst(1/getRealConst(args_new[1])); //PS. how to be with this part?
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
        opensmt::Real v1(sym_store.getName(getPterm(args[0]).symb()));
        opensmt::Real v2(sym_store.getName(getPterm(args[1]).symb()));
        if (v1 <= v2)
            return getTerm_true();
        else
            return getTerm_false();

    } else {

        // Should be in the form that on one side there is a constant
        // and on the other there is a sum
        PTRef tr_neg = mkNumNeg(args[0], msg);
        vec<PTRef> sum_args;
        sum_args.push(args[1]);
        sum_args.push(tr_neg);
        PTRef sum_tmp = mkNumPlus(sum_args, msg); // This gives us a collapsed version of the sum
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

        PTRef r = mkFun(sym_Num_LEQ, args, msg);
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
        opensmt::Real v1(rat_str1);
        opensmt::Real v2(rat_str2);
        free(rat_str1);
        free(rat_str2);
        if (v1 < v2) {
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
        opensmt::Real v1(rat_str1);
        opensmt::Real v2(rat_str2);
        free(rat_str1);
        free(rat_str2);
        if (v1 > v2)
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

PTRef LALogic::insertTerm(SymRef sym, vec<PTRef>& terms, char **msg)  //PS change this as if sym = sym_Num_NEG return as is???
{
    if (sym == sym_Num_NEG)
        return mkNumNeg(terms[0], msg);
    if (sym == sym_Num_MINUS)
        return mkNumMinus(terms, msg);
    if (sym == sym_Num_PLUS)
        return mkNumPlus(terms, msg);
    if (sym == sym_Num_TIMES)
        return mkNumTimes(terms, msg);
    if (sym == sym_Num_DIV)
        return mkNumDiv(terms, msg);
    if (sym == sym_Num_LEQ)
        return mkNumLeq(terms, msg);
    if (sym == sym_Num_LT)
        return mkNumLt(terms, msg);
    if (sym == sym_Num_GEQ)
        return mkNumGeq(terms, msg);
    if (sym == sym_Num_GT)
        return mkNumGt(terms, msg);
    if (sym == sym_Num_ITE)
        return mkIte(terms);

    return Logic::insertTerm(sym, terms, msg);
}

PTRef LALogic::mkConst(const char *name, const char **msg)
{
    return mkConst(getSort_num(), name);
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
        opensmt::Real v(tmp_str);
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
                if (is_neg)
                    asprintf(&out, "(/ (- %s) %s) <%d>", nom, den, tr.x);
                else
                    asprintf(&out, "(/ %s %s) <%d>", nom, den, tr.x);
            }
            else {
                if (is_neg)
                    asprintf(&out, "(/ (- %s) %s)", nom, den);
                else
                    asprintf(&out, "(/ %s %s)", nom, den);
            }
            free(nom);
            free(den);
        }
        else if (is_neg) {
            if (ext)
                asprintf(&out, "(- %s) <%d>", rat_str, tr.x);
            else
                asprintf(&out, "(- %s)", rat_str);
        }
        else
            out = rat_str;
    }
    else
        out = Logic::printTerm_(tr, ext, safe);
    return out;
}