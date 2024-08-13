//
// Created by Martin Blicha on 22.05.18.
//

#ifndef OPENSMT_FARKASINTERPOLATOR_H
#define OPENSMT_FARKASINTERPOLATOR_H

#include <common/Real.h>
#include <pterms/PtStructs.h>
#include <smtsolvers/TheoryInterpolator.h>

#include <iostream>

namespace opensmt {
class ArithLogic;

struct DecomposedStatistics {
    unsigned int decompositionOpportunities = 0;
    unsigned int decomposedItps = 0;
    unsigned int nonTrivialBasis = 0;
    unsigned int standAloneIneq = 0;

    void printStatistics(std::ostream & out) const {
        out << "\n###Decomposed statistics###\n"
            << "Total number of oportunities for decomposition: " << decompositionOpportunities << '\n'
            << "Total number of decomposed interpolants: " << decomposedItps << '\n'
            << "Out of total number of decomposed were (partly) trivially decomposable: " << standAloneIneq << '\n'
            << "Out of total number of decomposed had nontrivial basis of null space: " << nonTrivialBasis << '\n'
            << "###########################\n"
            << std::endl;
    }

    bool anyOpportunity() const { return decompositionOpportunities > 0; }

    void reset() {
        nonTrivialBasis = 0;
        decompositionOpportunities = 0;
        decomposedItps = 0;
        standAloneIneq = 0;
    }
};

class FarkasInterpolator {
public:
    using ItpColorMap = TheoryInterpolator::ItpColorMap;

    FarkasInterpolator(ArithLogic & logic, vec<PtAsgn> explanations, std::vector<Real> coeffs, ItpColorMap labels)
        : logic(logic),
          explanations(std::move(explanations)),
          explanation_coeffs(std::move(coeffs)),
          labels(std::move(labels)) {}

    FarkasInterpolator(ArithLogic & logic, vec<PtAsgn> explanations, std::vector<Real> coeffs, ItpColorMap labels,
                       std::unique_ptr<TermColorInfo> colorInfo)
        : logic(logic),
          explanations(std::move(explanations)),
          explanation_coeffs(std::move(coeffs)),
          labels(std::move(labels)),
          termColorInfo(std::move(colorInfo)) {}

    FarkasInterpolator(ArithLogic & logic, vec<PtAsgn> explanations, std::vector<Real> coeffs,
                       std::unique_ptr<TermColorInfo> colorInfo)
        : logic(logic),
          explanations(std::move(explanations)),
          explanation_coeffs(std::move(coeffs)),
          termColorInfo(std::move(colorInfo)) {}

    PTRef getFarkasInterpolant();
    PTRef getDualFarkasInterpolant();
    PTRef getFlexibleInterpolant(Real);
    PTRef getDecomposedInterpolant();
    PTRef getDualDecomposedInterpolant();

    static DecomposedStatistics stats;

private:
    PTRef getDecomposedInterpolant(icolor_t color);
    PTRef getFarkasInterpolant(icolor_t color);

    bool isLocalFor(icolor_t color, PTRef var) const { return getColorFor(var) == color; }

    bool isInPartitionOfColor(icolor_t color, PTRef atom) const {
        auto atomColor = getColorFor(atom);
        return (color & atomColor) != icolor_t::I_UNDEF;
    }

    icolor_t getColorFor(PTRef term) const {
        // use labels
        if (labels.find(term) != labels.end()) { return labels.at(term); }
        // otherwise use global partitioning information
        return getGlobalColorFor(term);
    }

    bool ensureHasColorForAllTerms();

    icolor_t getGlobalColorFor(PTRef term) const;

    PTRef weightedSum(std::vector<std::pair<PtAsgn, Real>> const & system);

    ArithLogic & logic;
    vec<PtAsgn> const explanations;
    std::vector<Real> const explanation_coeffs;
    ItpColorMap const labels;
    std::unique_ptr<TermColorInfo> termColorInfo;
};
} // namespace opensmt

#endif // OPENSMT_FARKASINTERPOLATOR_H
