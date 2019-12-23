//
// Created by Martin Blicha on 31.03.18.
//

#ifndef OPENSMT_TABLEAU_H
#define OPENSMT_TABLEAU_H


#include "Polynomial.h"
#include "LAVar.h"
#include "Real.h"

#include <unordered_map>
#include <set>
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
        auto beg = rows.rbegin() + (rows.size() - realSize);
        assert (std::distance(beg, rows.rend()) == realSize);
        auto it = std::find(beg, rows.rend(), row);
        assert(it != rows.rend());
        std::iter_swap(it, beg);
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
//    using vars_t = std::unordered_set<LVRef, LVRefHash>;
    using vars_t = std::set<LVRef, LVRefComp>;

public:
    void newNonbasicVar(LVRef v);
    void nonbasicVar(LVRef v);
    void newRow(LVRef v, std::unique_ptr<Polynomial> poly);
    std::size_t getNumOfCols() const;
    std::size_t getPolySize(LVRef basicVar) const;
    const opensmt::Real & getCoeff(LVRef basicVar, LVRef nonBasicVar) const;
    const column_t & getColumn(LVRef nonBasicVar) const;
    const Polynomial & getRowPoly(LVRef basicVar) const;
    Polynomial & getRowPoly(LVRef basicVar);
    const rows_t & getRows() const;

    void clear();
    void pivot(LVRef bv, LVRef nv);
    bool isBasic(LVRef v) const;
    bool isNonBasic(LVRef v) const;
    bool isQuasiBasic(LVRef v) const;

    bool isProcessed(LVRef v) const;

    void quasiToBasic(LVRef v);
    void basicToQuasi(LVRef v);

    // debug
    void print() const;
    bool checkConsistency() const;
    std::vector<LVRef> getNonBasicVars() const;

private:
    std::vector<std::unique_ptr<column_t>> cols;
    rows_t rows;

    enum class VarType:char {
        NONE, BASIC, NONBASIC, QUASIBASIC
    };
    std::vector<VarType> varTypes;
    void ensureTableauReadyFor(LVRef v);

    void addRow(LVRef v, std::unique_ptr<Polynomial> p);
    std::unique_ptr<Polynomial> removeRow(LVRef v);
    void moveRowFromTo(LVRef from, LVRef to);
    void moveColFromTo(LVRef from, LVRef to);
    void addRowToColumn(LVRef row, LVRef col) { assert(cols[col.x]); cols[col.x]->addRow(row); }
    void removeRowFromColumn(LVRef row, LVRef col) { assert(cols[col.x]); cols[col.x]->removeRow(row); }
    void clearColumn(LVRef col) { assert(cols[col.x]); cols[col.x]->clear();}
    void normalizeRow(LVRef row);
};



#endif //OPENSMT_TABLEAU_H
