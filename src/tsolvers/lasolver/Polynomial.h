//
// Created by Martin Blicha on 31.03.18.
//

#ifndef OPENSMT_POLYNOMIAL_H
#define OPENSMT_POLYNOMIAL_H

#include "LAVar.h"
#include "Real.h"
#include <vector>
#include <unordered_map>
#include <functional>

class Polynomial{
    friend class Tableau;
private:
    struct Term {
        LVRef var;
        opensmt::Real coeff;

        Term(LVRef var, opensmt::Real&& coeff): var{var.x}, coeff{std::move(coeff)} {}
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
    opensmt::Real removeVar(LVRef var);
    void negate();
    void divideBy(const opensmt::Real& r);

    template<typename ADD, typename REM>
    void merge(const Polynomial & other, const opensmt::Real & coeff, ADD informAdded, REM informRemoved) {
        std::vector<Term> storage;
        merge(other, coeff, informAdded, informRemoved, storage);
    }

    template<typename ADD, typename REM>
    void merge(const Polynomial & other, const opensmt::Real & coeff, ADD informAdded, REM informRemoved,
            std::vector<Term>& storage);

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

    iterator findTermForVar(LVRef var) {
        return std::find_if(poly.begin(), poly.end(), [var](const Term& term) { return term.var == var; });
    }

    void print() const;
};

template<typename ADD, typename REM>
void Polynomial::merge(const Polynomial &other, const opensmt::Real &coeff, ADD informAdded,
                  REM informRemoved, std::vector<Term>& storage) {
    if (storage.size() < this->poly.size() + other.poly.size()) {
        storage.resize(this->poly.size() + other.poly.size(), Term(LVRef_Undef, 0));
    }
    std::size_t storageIndex = 0;
    auto myIt = std::make_move_iterator(poly.begin());
    auto otherIt = other.poly.cbegin();
    auto myEnd = std::make_move_iterator(poly.end());
    auto otherEnd = other.poly.cend();
    TermCmp cmp;
    FastRational tmp;
    while(true) {
        if (myIt == myEnd) {
            for (auto it = otherIt; it != otherEnd; ++it) {
                storage[storageIndex].var = it->var;
                multiplication(storage[storageIndex].coeff, it->coeff, coeff);
                ++storageIndex;
                informAdded(it->var);
            }
            break;
        }
        if (otherIt == otherEnd) {
            std::move(myIt, myEnd, storage.begin() + storageIndex);
            storageIndex += myEnd - myIt;
            break;
        }
        if (cmp(*myIt, *otherIt)) {
            storage[storageIndex] = *myIt;
            ++storageIndex;
            ++myIt;
        }
        else if (cmp(*otherIt, *myIt)) {
            storage[storageIndex].var = otherIt->var;
            multiplication(storage[storageIndex].coeff, otherIt->coeff, coeff);
            ++storageIndex;
            informAdded(otherIt->var);
            ++otherIt;
        }
        else {
            assert(myIt->var == otherIt->var);
            multiplication(tmp, otherIt->coeff, coeff);
            myIt->coeff += tmp;
            if (myIt->coeff.isZero()) {
                informRemoved(myIt->var);
            }
            else {
                storage[storageIndex] = *myIt;
                ++storageIndex;
            }
            ++myIt;
            ++otherIt;
        }
    }
    std::vector<Term>(std::make_move_iterator(storage.begin()), std::make_move_iterator(storage.begin() + storageIndex)).swap(poly);
}

#endif //OPENSMT_POLYNOMIAL_H
