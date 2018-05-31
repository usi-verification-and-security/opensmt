//
// Created by Martin Blicha on 22.05.18.
//

#ifndef OPENSMT_LRA_INTERPOLATOR_H
#define OPENSMT_LRA_INTERPOLATOR_H

#include <PtStructs.h>
#include <Global.h>
#include <Real.h>

class LRALogic;

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
private:
    LRALogic & logic;
    const vec<PtAsgn> & explanations;
    const std::vector<opensmt::Real> & explanation_coeffs;
    const ipartitions_t & mask;
    std::map<PTRef, icolor_t> * labels;
};


#endif //OPENSMT_LRA_INTERPOLATOR_H
