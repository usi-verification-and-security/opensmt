//
// Created by Martin Blicha on 31.03.18.
//

#ifndef OPENSMT_POLYNOMIAL_H
#define OPENSMT_POLYNOMIAL_H

#include "LAVar.h"
#include "Real.h"
#include <vector>
#include <unordered_map>

struct MergeResult{
    std::vector<LVRef> added;
    std::vector<LVRef> removed;
};

class Polynomial{
private:
    struct Term {
        LVRef var;
        opensmt::Real coeff;

        Term(LVRef var, opensmt::Real&& coeff): var{var}, coeff{std::move(coeff)} {}
    };
    struct TermCmp {
        bool operator()(const Term& first, const Term& second) { return first.var.x < second.var.x; }
    };
//    using poly_t = std::unordered_map<LVRef, opensmt::Real, LVRefHash>;
    using poly_t = std::vector<Term>; // Terms are ordered by variable num
    poly_t poly;
public:
    void addTerm(LVRef var, opensmt::Real coeff);
    std::size_t size() const;
    const opensmt::Real & getCoeff(LVRef var) const;
    void removeVar(LVRef var);
    void negate();
    void divideBy(const opensmt::Real& r);
    MergeResult merge(const Polynomial & other, const opensmt::Real & coeff);

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
        return findTermForVar(var) != poly.end();
    }

    const_iterator findTermForVar(LVRef var) const {
        return std::find_if(poly.begin(), poly.end(), [var](const Term& term) { return term.var == var; });
    }

    void print() const;
};

#endif //OPENSMT_POLYNOMIAL_H
