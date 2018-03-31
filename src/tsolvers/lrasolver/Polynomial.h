//
// Created by Martin Blicha on 31.03.18.
//

#ifndef OPENSMT_POLYNOMIAL_H
#define OPENSMT_POLYNOMIAL_H

class Polynomial{
public:
    void addTerm(LVRef var, Real coeff);
    using iterator = std::vector<std::pair<LVRef, Real>>::iterator;
    using const_iterator = std::vector<std::pair<LVRef, Real>>::const_iterator;

    iterator begin(){
        throw std::logic_error("Not implemented yet!");
    }
    iterator end() {
        throw std::logic_error("Not implemented yet!");
    }

    const_iterator begin() const {
        throw std::logic_error("Not implemented yet!");
    }
    const_iterator end() const{
        throw std::logic_error("Not implemented yet!");
    }
};

#endif //OPENSMT_POLYNOMIAL_H
