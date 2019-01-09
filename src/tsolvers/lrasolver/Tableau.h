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
#include <memory>

class Column{
    std::vector<LVRef> rows;
    unsigned int realSize = 0;

    using iterator_t = std::vector<LVRef>::iterator;
    using const_iterator_t = std::vector<LVRef>::const_iterator;

public:
    void addRow(LVRef row) {
        assert(realSize <= rows.size());
        assert(std::find(rows.begin(), rows.begin() + realSize, row) == rows.begin() + realSize);
        if (realSize < rows.size()) {
            rows[realSize] = row;
        }
        else{
            rows.push_back(row);

        }
        ++realSize;
    }
    void removeRow(LVRef row) {
        assert(realSize > 0);
        assert(realSize <= rows.size());
        auto realEnd = rows.begin() + realSize;
        auto it = std::find(rows.begin(), realEnd, row);
        assert(it != realEnd);
        if (it == realEnd) {
            throw std::logic_error{"Removing row that is not present"};
        }
        std::iter_swap(it, realEnd - 1);
        --realSize;
    }

    void clear() {
        rows.clear();
        realSize = 0;
    }

    bool empty() const {
        return realSize == 0;
    }

    unsigned int size() const {
        return realSize;
    }

    iterator_t begin() { return rows.begin(); }
    iterator_t end() { return rows.begin() + realSize; }

    const_iterator_t begin() const { return rows.cbegin(); }
    const_iterator_t end() const { return rows.cbegin() + realSize; }

    const_iterator_t find(LVRef row) const { return std::find(begin(), end(), row); }


};

class Tableau{

protected:

    // using column_t = std::unordered_set<LVRef, LVRefHash>;
    using column_t = Column;
    using rows_t = std::vector<std::unique_ptr<Polynomial>>;
    using vars_t = std::unordered_set<LVRef, LVRefHash>;

public:
    void newNonbasicVar(LVRef v);
    void nonbasicVar(LVRef v);
    void newBasicVar(LVRef v, std::unique_ptr<Polynomial> poly);
    std::size_t getNumOfCols() const;
    std::size_t getPolySize(LVRef basicVar) const;
    const Polynomial& getPoly(LVRef basicVar) const;
    Polynomial& getPoly(LVRef basicVar);
    const opensmt::Real & getCoeff(LVRef basicVar, LVRef nonBasicVar) const;
    const column_t & getColumn(LVRef nonBasicVar) const;
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
    std::vector<std::unique_ptr<column_t>> cols;
    rows_t rows;

    vars_t basic_vars;
    vars_t nonbasic_vars;

    void addRow(LVRef v, std::unique_ptr<Polynomial> p);
    std::unique_ptr<Polynomial> removeRow(LVRef v);
    void moveRowFromTo(LVRef from, LVRef to);
    void moveColFromTo(LVRef from, LVRef to);
    void addRowToColumn(LVRef row, LVRef col) { assert(cols[col.x]); cols[col.x]->addRow(row); }
    void removeRowFromColumn(LVRef row, LVRef col) { assert(cols[col.x]); cols[col.x]->removeRow(row); }
    void clearColumn(LVRef col) { assert(cols[col.x]); cols[col.x]->clear();}
};



#endif //OPENSMT_TABLEAU_H
