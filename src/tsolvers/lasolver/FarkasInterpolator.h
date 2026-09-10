//
// Created by Martin Blicha on 22.05.18.
//

#ifndef OPENSMT_FARKASINTERPOLATOR_H
#define OPENSMT_FARKASINTERPOLATOR_H

#include <common/numbers/Real.h>
#include <pterms/PtStructs.h>
#include <smtsolvers/TheoryInterpolator.h>

#include <iostream>

namespace opensmt {
class ArithLogic;

// Defined in FarkasInterpolator.cc. `LATerm` is the paper's `LA(s <| 0, k)` value; `MixedSplit`
// is the (not-yet-lowered) result of splitting a mixed inequality literal into its A/B halves.
struct LATerm;
struct MixedSplit;

/// Per-mixed-variable metadata for the paper's `LA(s(x), k, F(x))` partial interpolant
/// ("Proof Tree Preserving Interpolation", Christ/Hoenicke/Nutz).
///
/// `getFarkasInterpolant` only produces a leaf partial interpolant, whose emitted form is the bare
/// inequality `s <| 0` (i.e. `F = (s <| 0)`). The parameters that a later pivot on the mixed literal
/// (`(rule-la)`, implemented in `LASolver::resolveMixed`) needs, but which are not recoverable from
/// that bare term, are collected here: the coefficient `c` of the auxiliary variable in `s` and the
/// parameter `k` (leaf value `-e`, written `-1` in the integer case).
struct MixedLAInfo {
    PTRef auxVar = PTRef_Undef; // the `.mixed_*` variable, free in the emitted partial interpolant
    Real coeff = 0;             // c > 0 : coefficient of `auxVar` in `s` (oriented to the `s <| 0` form)
    Real k = 0;                 // paper's k for this partial interpolant
    bool strict = false;        // whether the emitted inequality is strict
};

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

    // Metadata about the mixed auxiliary variables occurring in the partial interpolant produced by
    // the most recent getFarkasInterpolant()/getDualFarkasInterpolant() call. Consumed by
    // LASolver::resolveMixed when it pivots on the corresponding mixed literal.
    std::vector<MixedLAInfo> const & getMixedLAInfo() const { return mixedLAInfos; }

private:
    PTRef getDecomposedInterpolant(icolor_t color);
    PTRef getFarkasInterpolant(icolor_t color);
    MixedSplit splitMixedLiteral(PTRef leq);

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
    // Sum of `LA(s <| 0, k)` terms; the representation used by the mixed-literal (LIA) path.
    PTRef weightedSum(std::vector<LATerm> const & system);

    ArithLogic & logic;
    vec<PtAsgn> const explanations;
    std::vector<Real> const explanation_coeffs;
    ItpColorMap const labels;
    std::unique_ptr<TermColorInfo> termColorInfo;
    std::vector<MixedLAInfo> mixedLAInfos;
};
} // namespace opensmt

#endif // OPENSMT_FARKASINTERPOLATOR_H
