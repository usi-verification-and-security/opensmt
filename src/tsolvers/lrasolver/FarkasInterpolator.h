//
// Created by Martin Blicha on 22.05.18.
//

#ifndef OPENSMT_FARKASINTERPOLATOR_H
#define OPENSMT_FARKASINTERPOLATOR_H


#include <PtStructs.h>
#include <Global.h>
#include <Real.h>
#include <TheoryInterpolator.h>

class LALogic;
class PartitionManager;

struct DecomposedStatistics {
    unsigned int decompositionOpportunities = 0;
    unsigned int decomposedItps = 0;
    unsigned int nonTrivialBasis = 0;
    unsigned int standAloneIneq = 0;

    void printStatistics(std::ostream& out) const {
        out << "\n###Decomposed statistics###\n"
            << "Total number of oportunities for decomposition: " << decompositionOpportunities << '\n'
            << "Total number of decomposed interpolants: " << decomposedItps << '\n'
            << "Out of total number of decomposed were (partly) trivially decomposable: " << standAloneIneq << '\n'
            << "Out of total number of decomposed had nontrivial basis of null space: " << nonTrivialBasis << '\n'
            << "###########################\n"
            << std::endl;
    }

    bool anyOpportunity() const {return decompositionOpportunities > 0;}

    void reset() {
        nonTrivialBasis = 0;
        decompositionOpportunities = 0;
        decomposedItps = 0;
        standAloneIneq = 0;
    }
};

class FarkasInterpolator {
public:
    FarkasInterpolator(LALogic & logic, vec<PtAsgn> const & explanations, std::vector<opensmt::Real> const & coeffs,
                       std::map<PTRef, icolor_t> & labels) : FarkasInterpolator(logic, explanations, coeffs, &labels,
                                                                                nullptr) {}

    FarkasInterpolator(LALogic & logic, vec<PtAsgn> const & explanations, std::vector<opensmt::Real> const & coeffs,
                       std::map<PTRef, icolor_t> * labels, std::unique_ptr<TermColorInfo> colorInfo)
        : logic(logic),
          explanations(explanations),
          explanation_coeffs(coeffs),
          labels(labels),
          termColorInfo(std::move(colorInfo))
    {}

    PTRef getFarkasInterpolant();
    PTRef getDualFarkasInterpolant();
    PTRef getFlexibleInterpolant(opensmt::Real);
    PTRef getDecomposedInterpolant();
    PTRef getDualDecomposedInterpolant();

    static DecomposedStatistics stats;

private:

    PTRef getDecomposedInterpolant(icolor_t color);
    PTRef getFarkasInterpolant(icolor_t color);

    bool isLocalFor(icolor_t color, PTRef var) const{
        return getColorFor(var) == color;
    }

    bool isInPartitionOfColor(icolor_t color, PTRef atom) const {
        auto atomColor = getColorFor(atom);
        return (color & atomColor) != 0;
    }

    icolor_t getColorFor(PTRef term) const {
        // use labels
        if(labels != nullptr && labels->find(term) != labels->end()){
            return labels->at(term);
        }
        // otherwise use global partitioning information
        return getGlobalColorFor(term);
    }

    bool ensureHasColorForAllTerms();

    icolor_t getGlobalColorFor(PTRef term) const;

    PTRef weightedSum(std::vector<std::pair<PtAsgn, opensmt::Real>> const & system);

private:
    LALogic & logic;
    const vec<PtAsgn> & explanations;
    const std::vector<opensmt::Real> & explanation_coeffs;
    std::map<PTRef, icolor_t> * labels;
    std::unique_ptr<TermColorInfo> termColorInfo;
};

#endif //OPENSMT_FARKASINTERPOLATOR_H
