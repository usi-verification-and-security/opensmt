//
// Created by Martin Blicha on 31.03.18.
//

#ifndef OPENSMT_TABLEAU_H
#define OPENSMT_TABLEAU_H

#include "Polynomial.h"


class Tableau{

protected:
    class ColumnView{
    public:
        using iterator = std::vector<LVRef>::iterator;
        using const_iterator = std::vector<LVRef>::const_iterator;
        iterator begin();
        iterator end();
    };

public:
    void newNonbasicVar(LVRef v);
    void newBasicVar(LVRef v, Polynomial poly);
    std::size_t getNumOfCols() const;
    std::size_t getPolySize(LVRef basicVar) const;
    const Polynomial& getPoly(LVRef basicVar) const;
    const Real & getCoeff(LVRef basicVar, LVRef nonBasicVar) const;
    ColumnView getColumnView(LVRef nonBasicVar);
    void pivot(LVRef bv, LVRef nv);
};



#endif //OPENSMT_TABLEAU_H
