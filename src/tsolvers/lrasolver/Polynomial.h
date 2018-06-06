//
// Created by Martin Blicha on 31.03.18.
//

#ifndef OPENSMT_POLYNOMIAL_H
#define OPENSMT_POLYNOMIAL_H

#include "LAVar.h"
#include "Real.h"
#include <vector>
#include <unordered_map>

class Polynomial{
private:
    using poly_t = std::unordered_map<LVRef, opensmt::Real, LVRefHash>;
    poly_t poly;
public:
    void addTerm(LVRef var, opensmt::Real coeff);
    std::size_t size() const;
    const opensmt::Real & getCoeff(LVRef var) const;
    void removeVar(LVRef var);
    void negate();
    void divideBy(const opensmt::Real& r);
    std::pair<std::vector<LVRef>,std::vector<LVRef>> merge(const Polynomial & other, const opensmt::Real & coeff);

    using iterator = poly_t::iterator;
    using const_iterator = poly_t::const_iterator;

    iterator begin(){
        return poly.begin();
    }
    iterator end() {
        return poly.end();
    }

    const_iterator begin() const {
        return poly.cbegin();
    }
    const_iterator end() const{
        return poly.cend();
    }

    // debug
    bool contains(LVRef var) const {
        return poly.find(var) != poly.end();
    }
};

#endif //OPENSMT_POLYNOMIAL_H
