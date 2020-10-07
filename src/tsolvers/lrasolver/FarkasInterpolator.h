//
// Created by Martin Blicha on 22.05.18.
//

#ifndef OPENSMT_FARKASINTERPOLATOR_H
#define OPENSMT_FARKASINTERPOLATOR_H


#include <PtStructs.h>
#include <Global.h>
#include <Real.h>

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

enum class ItpAlg {
    STRONG, WEAK, FACTOR, DECOMPOSING, DECOMPOSING_DUAL, UNDEF
};

class FarkasItpOptions {
    ItpAlg algorithm;
    opensmt::Real stregthFactor;

public:
    FarkasItpOptions(ItpAlg alg) : algorithm(alg) {}
    FarkasItpOptions(ItpAlg alg, FastRational strengthFactor) : algorithm(alg), stregthFactor(std::move(strengthFactor))
        { assert(alg == ItpAlg::FACTOR); }

    ItpAlg getAlgorithm() const { return algorithm; }
    opensmt::Real getStrengthFactor() const { return stregthFactor; }

    static FarkasItpOptions useFarkasAlgorithm() { return FarkasItpOptions(ItpAlg::STRONG); }
    static FarkasItpOptions useDualFarkasAlgorithm() { return FarkasItpOptions(ItpAlg::WEAK); }
    static FarkasItpOptions useFlexibleFarkasAlgorithm(FastRational factor) { return FarkasItpOptions(ItpAlg::FACTOR, std::move(factor)); }
    static FarkasItpOptions useDecomposingFarkasAlgorithm() { return FarkasItpOptions(ItpAlg::DECOMPOSING); }
    static FarkasItpOptions useDualDecomposingFarkasAlgorithm() { return FarkasItpOptions(ItpAlg::DECOMPOSING_DUAL); }

};

class FarkasInterpolator {
public:
    FarkasInterpolator(LALogic & logic, PartitionManager & pmanager, vec<PtAsgn> const & explanations, std::vector<opensmt::Real> const & coeffs,
                       ipartitions_t const & mask, std::map<PTRef, icolor_t> * labels)
        : logic(logic),
          pmanager(pmanager),
          explanations(explanations),
          explanation_coeffs(coeffs),
          mask(mask),
          labels(labels)
    {}

    PTRef getInterpolant(FarkasItpOptions const &);

    static DecomposedStatistics stats;

private:

    PTRef getDecomposedInterpolant(icolor_t color);

    bool isLocalFor(icolor_t color, PTRef var) const{
        switch (color){
            case icolor_t::I_A:
                return isALocal(var);
            case icolor_t::I_B:
                return isBLocal(var);
            default:
                throw std::logic_error("Invalid argument in isLocalFor");
        }
    }

    bool isInPartitionOfColor(icolor_t color, PTRef atom) const {
        if(labels != nullptr && labels->find(atom) != labels->end()){
            return labels->at(atom) == color;
        }
        switch(color){
            case icolor_t::I_A:
                return isALocal(atom);
            case icolor_t::I_B:
                return isBLocal(atom);
            default:
                throw std::logic_error{"Invalid query in isInPartitionOfColor"};
        }
    }
    bool isALocal(PTRef var) const;
    bool isBLocal(PTRef var) const;

private:
    LALogic & logic;
    PartitionManager & pmanager;
    const vec<PtAsgn> & explanations;
    const std::vector<opensmt::Real> & explanation_coeffs;
    const ipartitions_t & mask;
    std::map<PTRef, icolor_t> * labels;
};

#endif //OPENSMT_FARKASINTERPOLATOR_H
