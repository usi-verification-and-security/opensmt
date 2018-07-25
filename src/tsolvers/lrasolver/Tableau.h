//
// Created by Martin Blicha on 31.03.18.
//

#ifndef OPENSMT_TABLEAU_H
#define OPENSMT_TABLEAU_H


#include "Polynomial.h"
#include "LAVar.h"
#include "Real.h"

#include <unordered_set>
#include <unordered_map>
#include <vector>
#include <functional>

class Tableau{

protected:
    using column_t = std::unordered_set<LVRef, LVRefHash>;
    using rows_t = std::unordered_map<LVRef, Polynomial, LVRefHash>;
    using vars_t = std::unordered_set<LVRef, LVRefHash>;

//    class ColumnView{
//    public:
//        using iterator = std::vector<LVRef>::iterator;
//        using const_iterator = std::vector<LVRef>::const_iterator;
//        iterator begin() {return ColumnViewIterator(colvar, tableau)}
//        iterator end();
//        ColumnView(LVRef colVar, const Tableau & tableau) : colvar{colVar}, tableau{tableau} {}
//    private:
//
//        LVRef colvar;
//        const Tableau & tableau;
//
//        class ColumnViewIterator{
//            const Tableau & tableau;
//            column_t::iterator it;
//            column_t::iterator end;
//        public:
//            ColumnViewIterator(, const Tableau & tableau) :
//                    tableau{tableau},
//                    it{tableau.cols.at(v).begin()},
//                    end{tableau.cols.at(v).end()}
//            {}
//            LVRef operator*() {return *it;}
//            void operator++() {++it; while(it != end && !tableau.isActive(*it)){++it;}}
//
//        };
//    };

public:
    void newNonbasicVar(LVRef v);
    void nonbasicVar(LVRef v);
    void newBasicVar(LVRef v, Polynomial poly);
    std::size_t getNumOfCols() const;
    std::size_t getPolySize(LVRef basicVar) const;
    const Polynomial& getPoly(LVRef basicVar) const;
    Polynomial& getPoly(LVRef basicVar);
    const opensmt::Real & getCoeff(LVRef basicVar, LVRef nonBasicVar) const;
    const column_t & getColumn(LVRef nonBasicVar);
    const rows_t & getRows() const;
    const vars_t & getNonBasicVars() const;

    void clear();
    void pivot(LVRef bv, LVRef nv);
    bool isActive(LVRef basicVar) const;
    bool isBasic(LVRef v) const;
    bool isNonBasic(LVRef v) const;

    bool isProcessed(LVRef v) const;

    // returns map of eliminated variables to their corresponding polynomials
    // NOTE: Variables eliminate sooner can contain variables eliminated later!
    std::vector<std::pair<LVRef, Polynomial>> doGaussianElimination(std::function<bool(LVRef)>);

    // debug
    void print() const;
    bool checkConsistency() const;

private:
    std::unordered_map<LVRef, column_t, LVRefHash> cols;
    rows_t rows;

    vars_t basic_vars;
    vars_t nonbasic_vars;

    void addRow(LVRef v, Polynomial p);
    void removeRow(LVRef v);



};



#endif //OPENSMT_TABLEAU_H
