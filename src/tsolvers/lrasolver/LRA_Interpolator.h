//
// Created by Martin Blicha on 22.05.18.
//

#ifndef OPENSMT_LRA_INTERPOLATOR_H
#define OPENSMT_LRA_INTERPOLATOR_H


#include <PtStructs.h>
#include <Global.h>
#include <Real.h>
#include <PartitionManager.h>

class LRALogic;

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

class LRA_Interpolator {
public:
    LRA_Interpolator(LRALogic & logic, vec<PtAsgn> const & explanations, std::vector<opensmt::Real> const & coeffs,
                     ipartitions_t const & mask, std::map<PTRef, icolor_t> * labels) : logic(logic),
                                                                                       explanations(explanations),
                                                                                       explanation_coeffs(coeffs),
                                                                                       mask(mask),
                                                                                       labels(labels)
    {}
    PTRef getInterpolant(icolor_t color, PartitionManager &);


    bool isLocalFor(icolor_t color, PTRef var, PartitionManager &pmanager) const{
        switch (color){
            case icolor_t::I_A:
                return isALocal(var, pmanager);
            case icolor_t::I_B:
                return isBLocal(var, pmanager);
            default:
                throw std::logic_error("Invalid argument in isLocalFor");
        }
    }

    bool isInPartitionOfColor(icolor_t color, PTRef atom, PartitionManager &pmanager) const {
        if(labels != nullptr && labels->find(atom) != labels->end()){
            return labels->at(atom) == color;
        }
        switch(color){
            case icolor_t::I_A:
                return isALocal(atom, pmanager);
            case icolor_t::I_B:
                return isBLocal(atom, pmanager);
            default:
                throw std::logic_error{"Invalid query in isInPartitionOfColor"};
        }
    }
    bool isALocal(PTRef var, PartitionManager &pmanager) const;
    bool isBLocal(PTRef var, PartitionManager &pmanager) const;

    static DecomposedStatistics stats;
private:
    LRALogic & logic;
    const vec<PtAsgn> & explanations;
    const std::vector<opensmt::Real> & explanation_coeffs;
    const ipartitions_t & mask;
    std::map<PTRef, icolor_t> * labels;


};

#endif //OPENSMT_LRA_INTERPOLATOR_H
