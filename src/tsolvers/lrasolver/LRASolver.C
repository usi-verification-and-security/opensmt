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

#ifdef PRODUCE_PROOF
#include "LRA_Interpolator.h"
#endif

static SolverDescr descr_lra_solver("LRA Solver", "Solver for Quantifier Free Linear Real Arithmetics");

LRASolver::LRASolver(SMTConfig & c, LRALogic& l, vec<DedElem>& d)
    : logic(l)
    , LASolver(descr_lra_solver, c, l, d)
    , delta(Delta::ZERO)

{
    status = INIT;
}


void LRASolver::clearSolver()
{

    LASolver::clearSolver();
    delta = Delta::ZERO;
}

void LRASolver::computeConcreteModel(LVRef v) {
    while (concrete_model.size() <= getVarId(v))
        concrete_model.push(nullptr);

    PTRef tr = lavarStore.getVarPTRef(v);
    auto it = removed_by_GaussianElimination.find(v);
    if(it != removed_by_GaussianElimination.end()){
        auto const & representation = (*it).second;
        Delta val;
        for (auto const & term : representation) {
            val += term.coeff * model.read(term.var);
        }
        concrete_model[getVarId(v)] = new opensmt::Real(val.R() + val.D() * delta);
    }
    else {
        concrete_model[getVarId(v)] = new opensmt::Real(model.read(v).R() + model.read(v).D() * delta);
    }
}

void LRASolver::doGaussianElimination( )
{
    auto eliminated = tableau.doGaussianElimination([this](LVRef v){return this->isUnbounded(v);});
    for(auto rit = eliminated.rbegin(); rit != eliminated.rend(); ++ rit) {
        auto entry = *rit;
        auto poly = entry.second;
        for(auto const & term : entry.second){
            auto var = term.var;
            auto it = removed_by_GaussianElimination.find(var);
            if( it != removed_by_GaussianElimination.end() && poly.contains(var)) {
                auto to_substitute = (*it).second;
                auto coeff = poly.getCoeff(var);
                poly.merge(to_substitute, coeff);
            }
        }
        removed_by_GaussianElimination.emplace(entry.first, poly);
    }
}

//
// Detect the appropriate value for symbolic delta and stores the model
//

void LRASolver::computeModel()
{
    assert( status == SAT );
    Delta delta_abst = Delta_PlusInf;  // We support plus infinity for this one.

    // Let x be a LV variable such that there are asserted bounds c_1 <= x and x <= c_2, where
    // (1) c_1 = (i1 | s1), c_2 = (i2 | -s2)
    // (2) s1, s2 \in {0, 1}
    // (3) val(x) = (R | D).
    // Then delta(x) := (i1+i2)/2 - R.
    // If x is not bounded from below or above, i.e., c_1 <= x, or x <= c_2, or neither, then
    // delta(x) := + Infty.
    // Now D at the same time is equal to k*\delta', and we need a value for \delta'.  So
    // \delta'(x) = D/k
    // Finally, \delta := min_{x \in LV |delta'(x)|}.

    for (unsigned i = 0; i < lavarStore.numVars(); ++i)
    {
        LVRef v {i};
        if (model.read(v).D() == 0)
            continue; // If values are exact we do not need to consider them for delta computation

        assert( !isModelOutOfBounds(v) );

        Delta D;

        if (model.Lb(v).isMinusInf() || model.Ub(v).isPlusInf())
            D = Delta_PlusInf;
        else
            D = (model.Lb(v).R() + model.Ub(v).R())/2 - model.read(v).R();

        D = D/model.read(v).D();

        if (D < 0) D.negate();

        if (delta_abst > D)
            delta_abst = D;

    }

    if (delta_abst.isPlusInf())
        delta = 1;
    else
        delta = delta_abst.R();

/*
    // TODO: check if it is it really true :)
    assert( minDelta >= 0 );
    assert( maxDelta <= 0 );
    delta = ( minDelta ) / 2;
*/

#ifdef GAUSSIAN_DEBUG
    cerr << "; delta: " << curDelta << '\n';
#endif

    for ( unsigned i = 0; i < lavarStore.numVars(); i++)
    {
        LVRef v {i};
        computeConcreteModel(v);
    }

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
    LVRef var = this->lavarStore.getVarByLeqId(logic.getPterm(ptref).getId());
    if (!model.hasModel(var)) { return l_Undef; }
    LABoundRefPair bounds = this->boundStore.getBoundRefPair(ptref);
    assert( bounds.pos != LABoundRef_Undef && bounds.neg != LABoundRef_Undef );
    auto const& val = model.read(var);
    bool positive = false;
    auto const& positive_bound = this->boundStore[bounds.pos];
    if ((positive_bound.getType() == bound_l && positive_bound.getValue() <= val)
        || (positive_bound.getType() == bound_u && positive_bound.getValue() >= val)) {
        positive = true;
    }
    bool negative = false;
    auto const& negative_bound = this->boundStore[bounds.neg];
    if ((negative_bound.getType() == bound_l && negative_bound.getValue() <= val)
        || (negative_bound.getType() == bound_u && negative_bound.getValue() >= val)) {
        negative = true;
    }
    // MB: Maybe we will not get any suggestion, if the value is <0|-1/2>, but the bounds are <0|0> and <0|-1>
//    assert(positive || negative);
    assert(!positive || !negative);
    if (positive) { return l_True; }
    if (negative) { return l_False; }
    return l_Undef;
}


#ifdef PRODUCE_PROOF


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

    for ( unsigned i = 0; i < explanation.size( ); i++ )
    {
        icolor_t color = I_UNDEF;
        const ipartitions_t & p = logic.getIPartitions(explanation[i].tr);
        Pterm& t = logic.getPterm(explanation[i].tr);
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
            PTRef nonconst_weak = interpolant_dual.getPTRefNonConstant();
            //cout << "; Constant Strong " << const_strong << endl;
            //cout << "; Constant Weak " << const_weak << endl;
            //cout << "; NonConstant Strong " << logic.printTerm(nonconst_strong) << endl;
            //cout << "; NonConstant Weak " << logic.printTerm(nonconst_weak) << endl;
            PTRef neg_strong = logic.mkNumNeg(nonconst_strong);
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

        char* msg;
        if (itpAlg != ItpAlg::WEAK)
        {
            if (delta_flag)
                itp = logic.mkNumLt(args, &msg);
            else
                itp = logic.mkNumLeq(args, &msg);
        }
        else
        {
            if (delta_flag_dual)
                itp = logic.mkNumLt(args, &msg);
            else
                itp = logic.mkNumLeq(args, &msg);
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

#endif // PRODUCE_PROOF

