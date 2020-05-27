/*********************************************************************
 Author:
   Leonardo Alt <leonardoaltt@gmail.com>
 , Antti Hyvarinen <antti.hyvarinen@gmail.com>
 , Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
 , Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

 OpenSMT2 -- Copyright (C)   2012 - 2016, Antti Hyvarinen
                             2008 - 2012, Roberto Bruttomesso

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

#include <unordered_map>
#include "LRASolver.h"
#include "LASolver.h"

#include "LA.h"

#include "LRA_Interpolator.h"

static SolverDescr descr_lra_solver("LRA Solver", "Solver for Quantifier Free Linear Real Arithmetics");

LRASolver::LRASolver(SMTConfig & c, LRALogic& l, vec<DedElem>& d)
    : LASolver(descr_lra_solver, c, l, d)
    , logic(l)
{
    status = INIT;
}


void LRASolver::clearSolver()
{
    LASolver::clearSolver();
}



Real LRASolver::getReal(PTRef r) {
    return logic.getNumConst(r);
}


//
// Performs the main Check procedure to see if the current constraints
// and Tableau are satisfiable
//
TRes LRASolver::check(bool complete) {

    if (check_simplex(complete))
        return TRes::SAT;
    else
        return TRes::UNSAT;

}

//
// Destructor
//
LRASolver::~LRASolver( )
{
}

LRALogic&  LRASolver::getLogic() { return logic; }


lbool LRASolver::getPolaritySuggestion(PTRef ptref) const {
    if (!this->isInformed(ptref)) { return l_Undef; }
    LVRef var = this->getVarForLeq(ptref);
    LABoundRefPair bounds = getBoundRefPair(ptref);
    assert( bounds.pos != LABoundRef_Undef && bounds.neg != LABoundRef_Undef );
    return simplex.getPolaritySuggestion(var, bounds.pos, bounds.neg);
}

/**
 * Given an imaginary inequality v ~ c (with ~ is either < or <=), compute the real bounds on the variable
 *
 * @param c Real number representing the upper bound
 * @param strict inequality is LEQ if false, LT if true
 * @return The real values of upper and lower bound corresponding to the inequality
 */
LABoundStore::BoundValuePair LRASolver::getBoundsValue(const Real & c, bool strict) {
    if (strict) {
        // v < c => UB is c-\delta, LB is c
        return { Delta(c, -1), Delta(c) };
    }
    else {
        // v <= c => UB is c, LB is c+\delta
        return { Delta(c), Delta(c, 1) };
    }
}




enum class ItpAlg {
    STRONG, WEAK, FACTOR, EXPERIMENTAL_STRONG, EXPERIMENTAL_WEAK, UNDEF
};
//
// Compute interpolants for the conflict
//
PTRef
LRASolver::getInterpolant( const ipartitions_t & mask , map<PTRef, icolor_t> *labels)
{
    // Old implementation:
    //l = config.logic == QF_LRA || config.logic == QF_UFLRA
    //? QF_LRA
    //: QF_LIA;

    assert(status == UNSAT);
    assert (explanation.size()>1);

    if(usingExperimental()){
        if (verbose() > 1){
            std::cerr << "; Using experimental LRA interpolation\n";
        }
        auto itp = getExperimentalInterpolant(mask, labels);
        assert(itp != PTRef_Undef);
        if(logic.isBooleanOperator(itp) || (logic.isNot(itp) && logic.isBooleanOperator(logic.getPterm(itp)[0]))){
            ++interpolStats.interestingInterpolants;
//            std::cerr << "; Interesting interpolant computed: " << logic.printTerm(itp) << '\n';
        }
        else{
            ++interpolStats.defaultInterpolants;
        }
        return itp;
    }

    const ItpAlg itpAlg = [this](){
        if(usingStrong()) {return ItpAlg::STRONG;}
        if(usingWeak()) {return ItpAlg::WEAK;}
        if(usingFactor()) {return ItpAlg::FACTOR;}
        return ItpAlg::UNDEF;
    }(); // note the parenthesis => immediate call of the lambda

    if (verbose() > 1)
    {
        if (itpAlg == ItpAlg::STRONG)
            cerr << "; Using Strong for LRA interpolation" << endl;
        else if (itpAlg == ItpAlg::WEAK)
            cerr << "; Using Weak for LRA interpolation" << endl;
        else if(itpAlg == ItpAlg::FACTOR)
            cerr << "; Using Factor " << getStrengthFactor() << " for LRA interpolation" << endl;
        else
            cerr << "; LRA interpolation algorithm unknown" << endl;
    }

    LAExpression interpolant(logic);
    LAExpression interpolant_dual(logic);
    bool delta_flag = false;
    bool delta_flag_dual = false;

#ifdef ITP_DEBUG
    vec<PTRef> tr_vec;
    for (int i = 0; i < explanation.size(); i++)
    {
        PTRef tr_vecel = explanation[i].tr;
        tr_vec.push(explanation[i].sgn == l_False ? logic.mkNot(tr_vecel) : tr_vecel);
    }
    PTRef tr = logic.mkAnd(tr_vec);
    printf("; Explanation: \n");
    printf(";  %s\n", logic.printTerm(tr));
#endif

    for ( int i = 0; i < explanation.size( ); i++ )
    {
        icolor_t color = I_UNDEF;
        const ipartitions_t & p = logic.getIPartitions(explanation[i].tr);
        if ( isAB( p, mask ) ) {
            color = I_AB;
        }
        else if ( isAlocal( p, mask ) ) {
            color = I_A;
        }
        else if ( isBlocal( p, mask ) ) {
            color = I_B;
        }
        if (color != I_A && color != I_AB && color != I_B)
        {
            printf("Error: color is not defined.\n");
            printf("  equation: %s\n", logic.printTerm(explanation[i].tr));
            printf("  mask: %s\n", mask.get_str().c_str());
            printf("  p: %s\n", p.get_str().c_str());
            assert(false);
        }
        assert( color == I_A
                || color == I_AB
                || color == I_B );

        PTRef exp_pt = explanation[i].tr;
        if(labels != nullptr && labels->find(exp_pt) != labels->end())
        {
            if(color != I_UNDEF){
                // Partitioning and labels can disagree under conditions that according to partitioning
                // the explanation can be in both parts, but the label can be more strict
//                std::cerr << "Color disagreement for term: " << logic.printTerm(explanation[i].tr) << '\n';
//                std::cerr << "Color from partitioning: " << color << '\n';
//                std::cerr << "Color from labels: " << labels->find(exp_pt)->second << '\n';
                assert(color == I_AB || color == labels->find(exp_pt)->second);
            }
            // labels have priority of simple partitioning information
            color = labels->find(exp_pt)->second;
            //cout << "; PTRef " << logic.printTerm(exp_pt) << " has Boolean color " << color << endl;
        }

        //assert( color == I_A || color == I_B );

        // Add the conflict to the interpolant (multiplied by the coefficient)
        if(color == I_A || color == I_AB)
        {
            if (explanation[i].sgn == l_False)
            {
                interpolant.addExprWithCoeff(LAExpression(logic, explanation[i].tr, false), explanationCoefficients[i]);
                delta_flag=true;
            }
            else
            {
                interpolant.addExprWithCoeff(LAExpression(logic, explanation[i].tr, false), -explanationCoefficients[i]);
            }
        }
        if(color == I_B || color == I_AB)
        {
            if (explanation[i].sgn == l_False)
            {
                interpolant_dual.addExprWithCoeff(LAExpression(logic, explanation[i].tr, false), explanationCoefficients[i]);
                // TODO: investigate where delta_flag_dual should be used and how it should be used properly
                delta_flag_dual=true;
            }
            else
            {
                interpolant_dual.addExprWithCoeff(LAExpression(logic, explanation[i].tr, false), -explanationCoefficients[i]);
            }
        }
    }

    //cout << "; INTERPOLANT " << interpolant << endl;
    //cout << "; INTERPOLANT IS TRUE " << (interpolant.isTrue() ? "true" : "false") << endl;
    //cout << "; INTERPOLANT IS FALSE " << (interpolant.isFalse() ? "true" : "false") << endl;
    PTRef itp;
    if (interpolant.isTrue() && !delta_flag)
        itp = logic.getTerm_true();
    else if (interpolant.isFalse() || ( interpolant.isTrue() && delta_flag ))
        itp = logic.getTerm_false();
    else
    {
        vec<PTRef> args;
        if (itpAlg == ItpAlg::FACTOR)
        {
            opensmt::Real const_strong = interpolant.getRealConstant();
            opensmt::Real const_weak = interpolant_dual.getRealConstant();
            PTRef nonconst_strong = interpolant.getPTRefNonConstant();
            //PTRef nonconst_weak = interpolant_dual.getPTRefNonConstant();
            //cout << "; Constant Strong " << const_strong << endl;
            //cout << "; Constant Weak " << const_weak << endl;
            //cout << "; NonConstant Strong " << logic.printTerm(nonconst_strong) << endl;
            //cout << "; NonConstant Weak " << logic.printTerm(nonconst_weak) << endl;
            //PTRef neg_strong = logic.mkNumNeg(nonconst_strong);
            //assert(neg_strong == nonconst_weak);

            opensmt::Real lower_bound = const_strong;
            opensmt::Real upper_bound = const_weak * -1;

            //cout << "; Lower bound is " << lower_bound << endl;
            //cout << "; Upper bound is " << upper_bound << endl;
            assert(upper_bound >= lower_bound);

            //cout << "; Strength factor from config is " << getStrengthFactor() << endl;
            opensmt::Real strength_factor(getStrengthFactor());
            if (strength_factor < 0 || strength_factor >= 1)
            {
                opensmt_error("LRA strength factor has to be in [0,1)");
            }
            opensmt::Real strength_diff = (upper_bound - lower_bound);
            //cout << "; Diff is " << strength_diff << endl;
            //cout << "; Factor is " << strength_factor << endl;
            opensmt::Real strength_delta = strength_diff * strength_factor;
            //cout << "; Delta is " << strength_delta << endl;
            opensmt::Real new_constant = lower_bound + (strength_diff * strength_factor);
            new_constant = new_constant * -1;
            //cout << "; New constant is " << new_constant << endl;
            args.push(logic.mkConst(new_constant));
            args.push(nonconst_strong);
        }
        else if (itpAlg == ItpAlg::STRONG)
        {
            args.push(logic.mkConst("0"));
            args.push(interpolant.toPTRef());
        }
        else if (itpAlg == ItpAlg::WEAK)
        {
            args.push(logic.mkConst("0"));
            args.push(interpolant_dual.toPTRef());
        }
        else
        {
            opensmt_error("Error: interpolation algorithm not set for LRA.");
        }

        if (itpAlg != ItpAlg::WEAK)
        {
            if (delta_flag)
                itp = logic.mkNumLt(args);
            else
                itp = logic.mkNumLeq(args);
        }
        else
        {
            if (delta_flag_dual)
                itp = logic.mkNumLt(args);
            else
                itp = logic.mkNumLeq(args);
            itp = logic.mkNot(itp);
        }
    }

    if (verbose() > 1)
    {
        cerr << "; LRA Itp: " << logic.printTerm(itp) << endl;
    }

    return itp;
}




PTRef LRASolver::getExperimentalInterpolant(const ipartitions_t &mask, map<PTRef, icolor_t> *labels) {
    LRA_Interpolator interpolator{logic, explanation, explanationCoefficients, mask, labels};
    icolor_t color = config.getLRAInterpolationAlgorithm() == itp_lra_alg_experimental_strong ? icolor_t::I_A : icolor_t::I_B;
    auto res = interpolator.getInterpolant(color);
    if(verbose() > 1){
        std::cerr << "; Experimental interpolation returned interpolant: " << logic.printTerm(res) << '\n';
    }
    return res;
}
