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

#include "FarkasInterpolator.h"

static SolverDescr descr_lra_solver("LRA Solver", "Solver for Quantifier Free Linear Real Arithmetics");

LRASolver::LRASolver(SMTConfig & c, LRALogic & l)
    : LASolver(descr_lra_solver, c, l)
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
#ifdef PRINT_DECOMPOSED_STATS
    if (LRA_Interpolator::stats.anyOpportunity()) {
        LRA_Interpolator::stats.printStatistics(std::cout);
        LRA_Interpolator::stats.reset(); // Reset after print so they are not cumulated across instances
    }
#endif // PRINT_DECOMPOSED_STATS
}

LRALogic&  LRASolver::getLogic() { return logic; }


lbool LRASolver::getPolaritySuggestion(PTRef ptref) const {
    if (!this->isInformed(ptref)) { return l_Undef; }
    LVRef var = this->getVarForLeq(ptref);
    LABoundRefPair bounds = getBoundRefPair(ptref);
    assert( bounds.pos != LABoundRef_Undef && bounds.neg != LABoundRef_Undef );
    return simplex.getPolaritySuggestion(var, bounds.pos, bounds.neg);
}



//
// Compute interpolants for the conflict
//
PTRef
LRASolver::getInterpolant( const ipartitions_t & mask , std::map<PTRef, icolor_t> *labels, PartitionManager &pmanager) {
    assert(status == UNSAT);
    vec<PtAsgn> explCopy;
    explanation.copyTo(explCopy);
    FarkasInterpolator interpolator(logic, std::move(explCopy), explanationCoefficients, labels ? *labels : std::map<PTRef, icolor_t>{},
                                    std::unique_ptr<TermColorInfo>(new GlobalTermColorInfo(pmanager, mask)));
    auto itpAlgorithm = config.getLRAInterpolationAlgorithm();
    if (itpAlgorithm == itp_lra_alg_strong) { return interpolator.getFarkasInterpolant(); }
    else if (itpAlgorithm == itp_lra_alg_weak) { return interpolator.getDualFarkasInterpolant(); }
    else if (itpAlgorithm == itp_lra_alg_factor) { return interpolator.getFlexibleInterpolant(opensmt::Real(config.getLRAStrengthFactor())); }
    else if (itpAlgorithm == itp_lra_alg_decomposing_strong) { return interpolator.getDecomposedInterpolant(); }
    else if (itpAlgorithm == itp_lra_alg_decomposing_weak) { return interpolator.getDualDecomposedInterpolant(); }
    else {
        assert(false); // Incoorrect value in config
        return interpolator.getFarkasInterpolant();
    }
}

