/*
 *  Copyright (c) 2018-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_TABLEAU_H
#define OPENSMT_TABLEAU_H

#include "LAVar.h"
#include "Polynomial.h"

#include <common/Real.h>

#include <algorithm>
#include <functional>
#include <memory>
#include <set>
#include <unordered_map>
#include <vector>

namespace opensmt {
class Tableau {
public:
    class Column {
    public:
        using iterator_t = std::vector<LVRef>::iterator;
        using const_iterator_t = std::vector<LVRef>::const_iterator;

        void addRow(LVRef row) { rows.push_back(row); }

        void removeRow(LVRef row) {
            auto beg = rows.rbegin();
            auto it = std::find(beg, rows.rend(), row);
            assert(it != rows.rend());
            std::iter_swap(it, beg);
            rows.pop_back();
        }

        void clear() { rows.clear(); }

        bool empty() const { return rows.empty(); }

        unsigned int size() const { return rows.size(); }

        iterator_t begin() { return rows.begin(); }
        iterator_t end() { return rows.end(); }

        const_iterator_t begin() const { return rows.cbegin(); }
        const_iterator_t end() const { return rows.cend(); }

        const_iterator_t find(LVRef row) const { return std::find(begin(), end(), row); }

    private:
        std::vector<LVRef> rows;
    };

    using Polynomial = PolynomialT<LVRef>;

    // using column_t = std::unordered_set<LVRef, LVRefHash>;
    using column_t = Column;
    using rows_t = std::vector<std::unique_ptr<Polynomial>>;

    void newNonbasicVar(LVRef v);
    void nonbasicVar(LVRef v);
    void newRow(LVRef v, std::unique_ptr<Polynomial> poly);
    std::size_t getNumOfCols() const;
    std::size_t getPolySize(LVRef basicVar) const;
    Real const & getCoeff(LVRef basicVar, LVRef nonBasicVar) const;
    column_t const & getColumn(LVRef nonBasicVar) const;
    Polynomial const & getRowPoly(LVRef basicVar) const;
    Polynomial & getRowPoly(LVRef basicVar);
    rows_t const & getRows() const;

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

protected:
    // using vars_t = std::unordered_set<LVRef, LVRefHash>;
    using vars_t = std::set<LVRef, LVRefComp>;

private:
    enum class VarType : char { NONE, BASIC, NONBASIC, QUASIBASIC };

    void ensureTableauReadyFor(LVRef v);

    void addRow(LVRef v, std::unique_ptr<Polynomial> p);
    std::unique_ptr<Polynomial> removeRow(LVRef v);
    void moveRowFromTo(LVRef from, LVRef to);
    void moveColFromTo(LVRef from, LVRef to);
    void addRowToColumn(LVRef row, LVRef col) {
        assert(cols[col.x]);
        cols[col.x]->addRow(row);
    }
    void removeRowFromColumn(LVRef row, LVRef col) {
        assert(cols[col.x]);
        cols[col.x]->removeRow(row);
    }
    void clearColumn(LVRef col) {
        assert(cols[col.x]);
        cols[col.x]->clear();
    }
    void normalizeRow(LVRef row);

    std::vector<std::unique_ptr<column_t>> cols;
    rows_t rows;

    std::vector<VarType> varTypes;

    Tableau::Polynomial::poly_t tmp_storage;
};
} // namespace opensmt

#endif // OPENSMT_TABLEAU_H
