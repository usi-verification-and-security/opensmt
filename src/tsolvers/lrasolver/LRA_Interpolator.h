//
// Created by Martin Blicha on 22.05.18.
//

#ifndef OPENSMT_LRA_INTERPOLATOR_H
#define OPENSMT_LRA_INTERPOLATOR_H

#ifdef PRODUCE_PROOF

#include <PtStructs.h>
#include <Global.h>
#include <Real.h>

class LRALogic;

struct DecomposedStatistics {
    unsigned int nonTrivialItps = 0;
    unsigned int decomposedItps = 0;
    unsigned int nonTrivialBasis = 0;
    unsigned int standAloneIneq = 0;

    void printStatistics(std::ostream& out) const {
        out << "\n###Decomposed statistics###\n"
            << "Total number of nontrivial interpolants produced: " << nonTrivialItps << '\n'
            << "Total number of decomposed interpolants: " << decomposedItps << '\n'
            << "Out of total number of decomposed were (partly) trivially decomposable: " << standAloneIneq << '\n'
            << "Out of total number of decomposed had nontrivial basis of null space: " << nonTrivialBasis << '\n'
            << "###########################\n"
            << std::endl;
    }

    bool hasNonTrivial() const {return nonTrivialItps > 0;}

    void reset() {
        nonTrivialBasis = 0;
        nonTrivialItps = 0;
        decomposedItps = 0;
    }
};

class LRA_Interpolator {
public:
    LRA_Interpolator(LRALogic & logic, vec<PtAsgn> const & explanations, std::vector<opensmt::Real> const & coeffs,
                     ipartitions_t const & mask, std::map<PTRef, icolor_t> * labels) : logic{logic},
                                                                                       explanations{explanations},
                                                                                       explanation_coeffs{coeffs},
                                                                                       mask{mask},
                                                                                       labels{labels}
    {}
    PTRef getInterpolant(icolor_t color);


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

    static DecomposedStatistics stats;
private:
    LRALogic & logic;
    const vec<PtAsgn> & explanations;
    const std::vector<opensmt::Real> & explanation_coeffs;
    const ipartitions_t & mask;
    std::map<PTRef, icolor_t> * labels;


};

#endif // PRODUCE_PROOF
#endif //OPENSMT_LRA_INTERPOLATOR_H
