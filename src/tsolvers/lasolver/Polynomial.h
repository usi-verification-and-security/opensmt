//
// Created by Martin Blicha on 31.03.18.
//

#ifndef OPENSMT_POLYNOMIAL_H
#define OPENSMT_POLYNOMIAL_H

#include "Real.h"
#include <vector>
#include <unordered_map>
#include <functional>
#include <iostream>

template<typename VarType>
class PolynomialT {
private:
    struct Term {
        VarType var;
        opensmt::Real coeff;

        Term(VarType var, opensmt::Real&& coeff): var{var.x}, coeff{std::move(coeff)} {}
    };
    struct TermCmp {
        bool operator()(const Term& first, const Term& second) { return first.var.x < second.var.x; }
    };
public:
    using poly_t = std::vector<Term>; // Terms are ordered by variable num
private:
    poly_t poly;
    static poly_t tmp_storage;
public:
    void addTerm(VarType var, opensmt::Real coeff);
    std::size_t size() const;
    const opensmt::Real & getCoeff(VarType var) const;
    opensmt::Real removeVar(VarType var);
    void negate();
    void divideBy(const opensmt::Real& r);

    template<typename ADD, typename REM>
    void merge(const PolynomialT & other, const opensmt::Real & coeff, ADD informAdded = [](VarType){}, REM informRemoved = [](VarType){},
            poly_t & storage = tmp_storage);

    using iterator = typename poly_t::iterator;
    using const_iterator = typename poly_t::const_iterator;

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
    bool contains(VarType var) const {
        return findTermForVar(var) != poly.end();
    }


    const_iterator findTermForVar(VarType var) const {
        return std::find_if(poly.begin(), poly.end(), [var](const Term& term) { return term.var == var; });
    }

    iterator findTermForVar(VarType var) {
        return std::find_if(poly.begin(), poly.end(), [var](const Term& term) { return term.var == var; });
    }

    void print() const;
};

template<typename VarType>
typename PolynomialT<VarType>::poly_t PolynomialT<VarType>::tmp_storage;

template<typename VarType>
template<typename ADD, typename REM>
void PolynomialT<VarType>::merge(const PolynomialT<VarType> &other, const opensmt::Real &coeff, ADD informAdded,
                  REM informRemoved, std::vector<Term>& storage) {
    if (storage.size() < this->poly.size() + other.poly.size()) {
        storage.resize(this->poly.size() + other.poly.size(), Term(VarType::Undef, 0));
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
    // At this point the right elements are in `storage`, from beginning to the `storageIndex`.
    // We need to get these elements to `this->poly`. Note that we never change the `storage` container, we just move out
    // the appropriate elements.
    // However, we observed that we need to shrink `poly` if its size is much smaller than the capacity.
    // The reason is that keeping large free capacity around for many rows blows up the memory
    // (worse case quadratic in the size of the tableau).
    auto polySize = poly.size();
    if (storageIndex > polySize) {
        // In this case we have more elements to move than the current size of the `poly` container.
        // We move the elements that fit the current `poly` size and then we insert the rest of the elements.
        std::move(storage.begin(), storage.begin() + polySize, poly.begin());
        poly.insert(poly.end(), std::make_move_iterator(storage.begin() + polySize), std::make_move_iterator(storage.begin() + storageIndex));
    }
    else if (/*storageIndex <= poly.size() and */ polySize <= 2 * storageIndex) {
        // In this case we have less elements that need to move than what we currently already have in `poly`, but not too litle.
        // We just move the appropriate elements and destroy the excess elements of `poly`.
        // Since we are removing too many elements, we avoid shrinking which would require re-allocation.
        std::move(storage.begin(), storage.begin() + storageIndex, poly.begin());
        poly.erase(poly.begin() + storageIndex, poly.end());
    } else { // poly.size() > 2 * storageIndex
        // This case is similar to case 2, but we have much less elements in the result than currently in `poly`.
        // To avoid too large free capacity in `poly`, we shrink its capacity to exactly the number of elements.
        // It is basically `poly.shrink_to_fit()`, except that `shrink_to_fit` is non-binding.
        std::vector<Term>(std::make_move_iterator(storage.begin()), std::make_move_iterator(storage.begin() + storageIndex)).swap(poly);
    }
}

template<typename VarType>
void PolynomialT<VarType>::addTerm(VarType var, opensmt::Real coeff) {
    assert(!contains(var));
    Term term {var, std::move(coeff)};
    auto it = std::upper_bound(poly.begin(), poly.end(), term, TermCmp{});
    poly.insert(it, std::move(term));
}

template<typename VarType>
unsigned long PolynomialT<VarType>::size() const {
    return poly.size();
}

template<typename VarType>
const FastRational &PolynomialT<VarType>::getCoeff(VarType var) const {
    assert(contains(var));
    return findTermForVar(var)->coeff;
}

template<typename VarType>
opensmt::Real PolynomialT<VarType>::removeVar(VarType var) {
    assert(contains(var));
    iterator it = findTermForVar(var);
    auto coeff = std::move(it->coeff);
    poly.erase(it);
    return coeff;
}

template<typename VarType>
void PolynomialT<VarType>::negate() {
    for(auto & term : poly) {
        term.coeff.negate();
    }
}

template<typename VarType>
void PolynomialT<VarType>::divideBy(const opensmt::Real &r) {
    for(auto & term : poly) {
        term.coeff /= r;
    }
}
template<typename VarType>
void PolynomialT<VarType>::print() const {
    for (auto & term : poly) {
        std::cout << term.coeff << " * " << term.var.x << "v + ";
    }
    std::cout << std::endl;
}
#endif //OPENSMT_POLYNOMIAL_H
