//
// Created by prova on 28.08.18.
//

#include "LIACutSolver.h"
#include "Matrix.h"

///COMPUTING EQUALITY BASIS



void LIACutSolver::pivotOnSmallestConsistentInPoly(LVRef var, Simplex& eqBasisSimplex) {
    assert(eqBasisSimplex.isBasic(var));
    LVRef v_found = LVRef_Undef;
    for (auto const &term : eqBasisSimplex.getRowPoly(var)) {
        auto var_nonbasic = term.var;
        assert(eqBasisSimplex.isNonBasic(var_nonbasic));
        assert(var_nonbasic != var);
        auto const &coeff = term.coeff;
        const bool is_coeff_zero = (coeff == 0);
        if (!is_coeff_zero && (model.Lb(var_nonbasic) < model.Ub(var_nonbasic))) {
            if (v_found != LVRef_Undef) {
                v_found = var_nonbasic;
                eqBasisSimplex.pivot(var, var_nonbasic);
            }
        }
    }
}

void LIACutSolver::initialize(Simplex& eqBasisSimplex, LRAModel& eqBasisModel) {
    //for all vars be it basic or non-basic
    const vec<LVRef> & allVars = eqBasisModel.getAllVars();
    for (int i = 0; i < allVars.size(); i++) {
        LVRef var = allVars[i];
        if (eqBasisModel.read(var) > eqBasisModel.Lb(var)) {
            eqBasisModel.clearLBound(var);
        }
        if (eqBasisModel.read(var) < eqBasisModel.Ub(var)) {
            eqBasisModel.clearUBound(var);
        }
        if ((eqBasisModel.read(var).hasDelta())) {
            eqBasisModel.clearUBound(var);
            eqBasisModel.clearLBound(var);
        }
    }

    for (auto var : eqBasisSimplex.getBasicVars()) {
        //for basicvar in basic
        if (eqBasisModel.Lb(var) == eqBasisModel.Ub(var))
            pivotOnSmallestConsistentInPoly(var, eqBasisSimplex);
    }

    for (int i = 0; i < allVars.size(); i++) {
        LVRef var = allVars[i];
        if (eqBasisModel.Lb(var) >= eqBasisModel.Ub(var))
            continue;

        //for x_k in basic union nonbasic
        if (!eqBasisModel.Lb(var).isMinusInf()){//this checks if lower bound of var is minus infinite
            //l_k := l_k +sigma
            eqBasisModel.tightenLBound(var);
            //assert(eqBasisModel.Lb(var).getType() == bound_l);
            assert(eqBasisModel.readLBound(var).getType() == bound_l);
        }
        if (!eqBasisModel.Ub(var).isPlusInf()){
            //u_k := u_k - sigma
            eqBasisModel.tightenUBound(var);
            //assert(eqBasisModel.Ub(var).getType() == bound_u);
            assert(eqBasisModel.readUBound(var).getType() == bound_l);
        }

        // What's the point of these?
        if (!eqBasisModel.Lb(var).isMinusInf() && eqBasisSimplex.isNonBasic(var)){
            eqBasisSimplex.changeValueBy(var, eqBasisModel.Lb(var));
        }
        if (!eqBasisModel.Ub(var).isPlusInf() && eqBasisSimplex.isNonBasic(var)){
            //updateValues(x_k, u_k)
            eqBasisSimplex.changeValueBy(var, eqBasisModel.Ub(var));
        }
    }
}

void LIACutSolver::fixEqualities(LVRef basicVar, Simplex& s, LRAModel& m){
    //input is basic var that explains the conflict form Simplex when it returns UNSAT
    //turns tightly bounded vars into explicit equalities
    assert(s.isBasic(basicVar));
    //for var that belongs to Nonbasic vars
    for (auto const &term : s.getRowPoly(basicVar)) {
        auto var = term.var;
        assert(s.isNonBasic(var));
        assert(var != basicVar);
        auto const &coeff = term.coeff;
        const bool is_coeff_pos = coeff > 0;
        if (m.Lb(var) < m.Ub(var)) {
            if (is_coeff_pos && m.read(basicVar) < m.Lb(basicVar)) {
                m.relaxUBound(var);
                m.setLBoundToUBound(var);
                s.changeValueBy(var, m.Ub(var));
            } else if (!is_coeff_pos && m.read(basicVar) < m.Lb(basicVar)) {
                m.relaxLBound(var);
                m.setUBoundToLBound(var);
                s.changeValueBy(var, m.Lb(var));
            } else if (is_coeff_pos && m.read(basicVar) > m.Ub(basicVar)) {
                m.relaxLBound(var);
                m.setUBoundToLBound(var);
                s.changeValueBy(var, m.Lb(var));
            } else if (!is_coeff_pos && m.read(basicVar) > m.Ub(basicVar)) {
                m.relaxUBound(var);
                m.setLBoundToUBound(var);
                s.changeValueBy(var, m.Ub(var));
            }
        }
    }
    if (m.read(basicVar) > m.Ub(basicVar)) {
        m.relaxUBound(basicVar);
        m.setLBoundToUBound(basicVar);
    }
    if (m.read(basicVar) < m.Lb(basicVar)) {
        m.relaxLBound(basicVar);
        m.setUBoundToLBound(basicVar);
    }
}
///END of supporting functions for computing equality basis


std::unique_ptr<Simplex> LIACutSolver::computeEqualityBasis(){
    //creating new simplex object
    std::unique_ptr<LRAModel> eqBasisModel = model.copyFlat(); // copy the model as a snapshot of the most recent values
    //Simplex eqBasisSimplex(config, *eqBasisModel, boundStore); // Create a new simplex from the model
    auto eqBasisSimplex = std::unique_ptr<Simplex>(new Simplex(config, *eqBasisModel, boundStore));
    eqBasisSimplex->initFromSimplex(simplex);  // Initialize the new simplex (mostly tableau) from the old simplex
    initialize(*eqBasisSimplex, *eqBasisModel); //removes all bounds that cannot produce equalities and turns Ax<=b to Ax<b
    //we call check again on the problem returned by Initialise function
    //(now all problems in our constraint system are strictly bounded, i.e. Ax<b)
    //if Ax<b is UNSAT then AX<=b implies equality

    std::vector<LABoundRef> explanationBounds;
    while (eqBasisSimplex->checkSimplex(explanationBounds, explanationCoefficients) == false) { // checkSimplexForStrictInequalSystem() Simplex work on tableau and bounds, when we call coreSimplex
        //it does computation on current state of the tableau
        //get x_i that explains conflict
        LABoundRef br = explanationBounds[0];
        LVRef basicVar = boundStore[br].getLVRef();
        fixEqualities(basicVar, *eqBasisSimplex, *eqBasisModel); //takes as input basic var explaining conflict - row x_i
        //and all vars x_j in row x_i with non-zero coefficient hold tightly
        for (auto const &term: eqBasisSimplex->getRowPoly(basicVar)) {//taking all the polynomials where this basic var is, but tableau contains non-basic vars..
            auto n_var = term.var;
            eqBasisSimplex->eliminateEquality(basicVar, n_var); //simplex.elliminate equal
        }
     }

    return eqBasisSimplex;
    //after while loop ends we remain with a system (stored in tableau) which is Double Bounded
}



///ALGORITHM STEPS:
//1. Identify explicit equalities
//2. Determine satisfiability of system by checking if solution for explicit equalities exists using SNF.
// If YES continue to step 3, else UNSAT and Terminate
//3. Compute equality basis to transform the system to be double bounded.
// If Simplex in this step returns SAT, continue to step 4, else UNSAt and Terminate
//4. Transfer double bounded system using HNF and call Simplex. If SAT then continue to step 5, else UNSAT and Terminate
//5. Call procedure checkIntegerAndSplit, if solution integer then SAT, else continue to step 6
//6. Compute new cuts of the form p<mu Or p=mu Or p>mu and send to SAT Solver that is augmented with Lookahead

TRes LIACutSolver::check(bool complete) {

    /// 1. Identify explicit equalities
    ///2. Determine satisfiability of system by checking if solution for explicit equalities exists using SNF.

    bool val = explicitEqualityCheck();
    if (val == false)
        return TRes::UNSAT;

    ///3.Compute equality basis to transform the system to be double bounded
    // If Simplex in this step returns SAT, continue to step 4, else UNSAt and Terminate
    //4. Compute equality basis (implicit equalities), this method eliminates equalities and
    // thus transforms system to be double-bounded (after elimination of equalities we remain
    // with inequalities, which are guaranteed to be double-bounded)
    bool rval = check_simplex(complete); // Compute a rational solution using simplex for the entire query (check_simplex from LASolver)
    //here is the first time when tableau is created
    if (rval == false)
        setStatus(UNSAT);
        return TRes::UNSAT; // function stops here and returns False
    //PS is this indentation correct?

    std::unique_ptr<Simplex> eqBasisSimplex = computeEqualityBasis();

    //after while loop ends we remain with a system (stored in tableau) which is Double Bounded
    //we have to store the tableau in new matrix A (input for transferring to HNF) which entries are integers

    int num_rows, num_cols;
    vec<LVRef> colToVar;
    ms.clear();

    MId A = eqBasisSimplex->getIntegerMatrix(ms, num_rows, num_cols, colToVar);


    ///END of step 3

    ///4.Transfer double bounded system using HNF and call Simplex.

    MId H = ms.getNewMatrix(num_rows, num_cols);
    ms.compute_hnf(H, A);

    //get tableau from matrix H and run simplex if sat then call checkIntegersAndSplit, else UNSAT
    //create a model
    std::unique_ptr<LRAModel> matrixModel;
    for (int i = 1; i <= ms[H].nCols(); i++) {
        LVRef v = colToVar[i - 1]; //basic vars?
        matrixModel->addVar(v);
    }
    // Create a new simplex from the model
    Simplex matrixSimplex(config, *matrixModel, boundStore);
    // Initialize the new simplex (mostly tableau)
    matrixSimplex.initFromSimplex(matrixSimplex);

    std::vector<LABoundRef> explanationBounds;
    explanationBounds.clear();
    if (matrixSimplex.checkSimplex(explanationBounds, explanationCoefficients) == true)
        return checkIntegersAndSplit(matrixSimplex, *matrixModel);
    else
        return TRes::UNSAT;
    //something needs to be done about explanations

    ///END of step 4

    //not needed!!! - then restoring the original bounds (for all vars x_i with l_i < u_i we
    //need to recover their old bounds)
    //backtrack
}

///5. Call procedure checkIntegerAndSplit and 6. Compute new cuts of the form p<mu Or p=mu Or p>mu

TRes LIACutSolver::checkIntegersAndSplit(Simplex& matrixSimplex, LRAModel& matrixModel) {
    //vec<opensmt::Real> v_r;
    //v_r.growTo(vars.elems()); //vars store equalities vars
    Map<LVRef, opensmt::Real, LVRefHash> int_valuation;
    vec<LVRef> evaluated_vars;

    // Collect the integer valuation to int_valuation.  This is done in two steps.
    // a. Collect the variables that are not bound by equalities, and simply round them.
    // b. Collect the variables that are bound by equalities, and compute their solution from the Smith decomposition (phase 5 below).
    for (int i = 0; i < int_vars.size(); i++) {
        computeConcreteModel(int_vars[i]);
        //if (vars.has(int_vars[i])) { //deals with equality part
        //  int col = vars[int_vars[i]];
        //v_r[col - 1] = *concrete_model[lvs[int_vars[i]].ID()];
        //} else {
        //opensmt::Real *r = concrete_model[lvs[int_vars[i]].ID()];
        opensmt::Real *r = concrete_model[getVarId(int_vars[i])];

        int_valuation.insert(int_vars[i], fastrat_round_to_int(*r));
        evaluated_vars.push(int_vars[i]);
        //}
    }
    //LAVecRef v = vecStore.getNewVec(v_r);

    /*
    // 5. Compute w = R^-1[Rv] (for the equality part)
    LAVecRef w_tmp = ms.mul_vector(R, v);
    LAVecRef w_tmp_int = ms.discretize(w_tmp);
    LAVecRef w = ms.mul_vector(Ri, w_tmp_int);

    for (int i = 0; i < vecStore[w].size(); i++) {
        LVRef v = colToVar[i];
        int_valuation.insert(v, vecStore[w][i + 1]);
        evaluated_vars.push(v);
    }
    */

    // The integer valuation is now in int_valuation.

    // 1. Check if int_valuation is a solution to the original LIA query

    //then u have values for every variable in int valuation
    //take the value of that variable and compare to the bound L or U
    //if the value is less than L bound or greater than upper bound, then no solution
    for (int i = 0; i < evaluated_vars.size(); i++) {
        LVRef v = evaluated_vars[i];
        if ((int_valuation[v] < matrixModel.readLBound(v).getValue()) ||
            (int_valuation[v] > matrixModel.readUBound(v).getValue())) {
            opensmt::Real mu;
            //only call eval_poly if v is basic

            if (matrixSimplex.isBasic(v)) {

                mu = matrixSimplex.getRowPoly(v).eval_poly(int_valuation);
            } else {

                mu = int_valuation[v];
            }

            vec<PTRef> or_args;

            // a <-> p<=mu AND p>=mu
            //Clauses that we send to SAT solver:
            //1. not(p<=mu) OR not(mu<=p) OR a
            //2. not(a) OR p<=mu
            //3. not(a) OR mu<=p

            //PTRef p_leq_mu = logic.mkNumLeq(lvs[v].getPTRef(), logic.mkConst(mu));
            PTRef p_leq_mu = logic.mkNumLeq(getVarPTRef(v), logic.mkConst(mu));

            //PTRef mu_leq_p = logic.mkNumLeq(logic.mkConst(mu), lvs[v].getPTRef());
            PTRef mu_leq_p = logic.mkNumLeq(logic.mkConst(mu), getVarPTRef(v));

            //PTRef a = logic.mkAnd(logic.mkNumLeq(lvs[v].getPTRef(), logic.mkConst(mu)), logic.mkNumGeq(lvs[v].getPTRef(), logic.mkConst(mu)));
            PTRef a = logic.mkAnd(logic.mkNumLeq(getVarPTRef(v), logic.mkConst(mu)),
                                  logic.mkNumGeq(getVarPTRef(v), logic.mkConst(mu)));

            or_args.push(logic.mkNot(p_leq_mu)); // not(p<=mu)
            or_args.push(logic.mkNot(mu_leq_p)); // not(mu<=p)
            or_args.push(a); // a <-> p<=mu AND p>=mu
            PTRef constr1 = logic.mkOr(or_args);
            PTRef constr2 = logic.mkOr(logic.mkNot(a), p_leq_mu);
            PTRef constr3 = logic.mkOr(logic.mkNot(a), mu_leq_p);
            PTRef constr = logic.mkAnd({constr1, constr2, constr3});

            printf("LIACutSolver constraint %s\n", logic.pp(constr));

            splitondemand.push(constr);
            setStatus(NEWSPLIT);
            return TRes::SAT;
        }
    }

    setStatus(SAT);
    return TRes::SAT;
}

///END of steps 5 and 6

bool LIACutSolver::explicitEqualityCheck() {


/// 1. Identify explicit equalities
///2. Determine satisfiability of system by checking if solution for explicit equalities exists using SNF.

// 1. Identify all equalities
        const vec<LVRef> &equalities = model.getEqualities();

// 2. Multiply them so that their coeffs are integers
        vec<Real> multiplicands; // These are the per-equality multiplicands
//    Map<LVRef,int,LVRefHash> vars; // Maps a LVRef to its column in the matrix U
        vars.clear();
        colToVar.clear();
        int column_count = 0;
        for (int i = 0; i < equalities.size(); i++) {
            LVRef eq_var = equalities[i];
            if (!vars.has(eq_var)) {
                colToVar.push(eq_var);
                vars.insert(eq_var, ++column_count);
            }

            const Delta &is_equal_to = model.Lb(eq_var);
            assert(is_equal_to == model.Ub(eq_var));
            assert(!is_equal_to.hasDelta()); // Delta'd values can never be equalities.

// Collect the non-unit coefficients to the vector reals
            vec<Real> reals;
            if (is_equal_to.R().get_den() != 1) // denominator cannot be -1
                reals.push(is_equal_to.R());

// Only basic variables have polynomials.  Non-basic variables have the factor 1
            if (simplex.isBasic(eq_var)) {
                for (auto const &term : simplex.getRowPoly(eq_var)) {
                    if (!vars.has(term.var)) {
                        colToVar.push(term.var);
                        vars.insert(term.var, ++column_count);
                    }
                    if (term.coeff.get_den() != 1) {
                        reals.push(term.coeff);
                    }
                }
            }

// Get the number that the equality needs to be multiplied so that factors are integers
            multiplicands.push(get_multiplicand(reals));
        }
//    printf("I need to construct a U = %d x %d matrix now.\n", equalities.size(), vars.getSize());


        ms.clear();
        vecStore.clear();
        va.clear();

        assert(vars.getSize() == colToVar.size());

        int n = vars.getSize(); //P.S. this is column
        int k = equalities.size(); //P.S. this is row

        MId U = ms.getNewMatrix(k, n);
        LAVecRef d = vecStore.getNewVec(equalities.size());
// Note here that we address matrices with U[i, j], where j is the col and i is the row.
        for (int i = 0; i < k; i++) {
            LVRef eq_var = equalities[i];
// Fill the result vector
// XXX We assume here that the result is an integer, but this is not true for some reason.
            vecStore[d][i + 1] = model.Lb(eq_var).R() * multiplicands[i];
            ms.MM(U, i + 1,
                  vars[eq_var]) = -multiplicands[i]; // - fac(eq_var) * multiplicands[i], where fac(eq_var) == 1

            if (simplex.isBasic(eq_var)) {
                for (auto const &term : simplex.getRowPoly(eq_var)) {
// Fill the row i+1 of the matrix U
                    ms.MM(U, i + 1, vars[term.var]) = term.coeff * multiplicands[i];
                }
            }

        }

// 3. Compute R from U = LSR Using the Smith normal form

        MId L = ms.getNewMatrix(k, k);
        MId Li = ms.getNewMatrix(k, k);
        MId R = ms.getNewMatrix(n, n);
        MId Ri = ms.getNewMatrix(n, n);

        MId S = ms.getNewMatrix(k, n);
        assert(ms[U].nRows() == ms[S].nRows());
        assert(ms[U].nCols() == ms[S].nCols());

        int dim;

        ms.compute_snf(U, S, dim, L, Li, R, Ri); //dim is the size of Smith Normal Form
#ifndef NDEBUG
        int ok = true;
        for (int i = 1; i <= ms[S].nRows() && ok; i++) {
            for (int j = 1; j <= ms[S].nCols() && ok; j++) {
                if ((i == j) != (ms.MM(S, i, j) != 0)) {
                    printf("Input matrix:\n%s\n", ms.print(U));
                    printf("Resulted in matrix:\n%s\n", ms.print(S));
                    assert(false);
                    ok = false;
                    break;
                }
            }
        }
#endif

//Compute L^-1d
        LAVecRef y = ms.mul_vector(Li, d);

// if (S[ai] % y[i] == 0) && for r<i<=k the ith component of y is zero then SAT, else UNSAT


        int i;
        for (i = 1; i <= dim; i++) {
            if (!(((ms.MM(S, i, i) != 0) && (vecStore[y][i] % ms.MM(S, i, i) == 0)) || ((ms.MM(S, i, i) == 0) &&
                                                                                        (vecStore[y][i] == 0)))) {
                printf("No integer solution. \n");
                printf("Original:\n%s\n", ms.print(U));
                printf("The integer vector of constants:\n%s\n", vecStore.print(d));
                printf("SNF:\n%s\n", ms.print(S));
                printf("The vector:\n%s\n", vecStore.print(y));
                MId s = ms.getNewMatrix(1, ms[Li].nCols());
                for (int j = 1; j <= ms[Li].nCols(); j++) {
                    ms.MM(s, 1, j) = ms.MM(Li, i, j);
                }
                MId sU = ms.mul_matrix(s, U);
                opensmt::Real sd = vecStore[ms.mul_vector(s, d)][1];

                for (int j = 1; j <= ms[sU].nCols(); j++) {
                    if (ms.MM(sU, 1, j) != 0) {
                        PtAsgn e1, e2;
                        e1 = getAsgnByBound(model.readLBoundRef(colToVar[j - 1]));
                        e2 = getAsgnByBound(model.readUBoundRef(colToVar[j - 1]));
                        explanation.push(e1);
                        explanation.push(e2);

                    }

                }

//#ifndef NDEBUG
                char *exp_string = (char *) malloc(1);
                exp_string[0] = '\0';
                for (int j = 0; j < explanation.size(); j++) {
                    char *tmp;
                    asprintf(&tmp, "%s %s%s", exp_string,
                             explanation[j].sgn == l_True ? "" : "not ", logic.pp(explanation[j].tr));
                    free(exp_string);
                    exp_string = tmp;
                }

                printf("(and %s)\n", exp_string);
                free(exp_string);
//#endif
                setStatus(UNSAT);
                break;
                //return TRes::UNSAT;

            } /*else {
                setStatus(SAT);
            }*/

        }


        return getStatus();
/// END OF step 1 and 2

}