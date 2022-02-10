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

class Tableau{

    class Column{
        std::vector<LVRef> rows;

        using iterator_t = std::vector<LVRef>::iterator;
        using const_iterator_t = std::vector<LVRef>::const_iterator;

    public:
        void addRow(LVRef row) {
            rows.push_back(row);
        }
        void removeRow(LVRef row) {
            auto beg = rows.rbegin();
            auto it = std::find(beg, rows.rend(), row);
            assert(it != rows.rend());
            std::iter_swap(it, beg);
            rows.pop_back();
        }

        void clear() {
            rows.clear();
        }

        bool empty() const {
            return rows.empty();
        }

        unsigned int size() const {
            return rows.size();
        }

        iterator_t begin() { return rows.begin(); }
        iterator_t end() { return rows.end(); }

        const_iterator_t begin() const { return rows.cbegin(); }
        const_iterator_t end() const { return rows.cend(); }

        const_iterator_t find(LVRef row) const { return std::find(begin(), end(), row); }
    };

protected:

    // using column_t = std::unordered_set<LVRef, LVRefHash>;
    using column_t = Column;
    using rows_t = std::vector<std::unique_ptr<Polynomial<LVRef>>>;
//    using vars_t = std::unordered_set<LVRef, LVRefHash>;
    using vars_t = std::set<LVRef, LVRefComp>;

public:
    void newNonbasicVar(LVRef v);
    void nonbasicVar(LVRef v);
    void newRow(LVRef v, std::unique_ptr<Polynomial<LVRef>> poly);
    std::size_t getNumOfCols() const;
    std::size_t getPolySize(LVRef basicVar) const;
    const opensmt::Real & getCoeff(LVRef basicVar, LVRef nonBasicVar) const;
    const column_t & getColumn(LVRef nonBasicVar) const;
    const Polynomial<LVRef> & getRowPoly(LVRef basicVar) const;
    Polynomial<LVRef> & getRowPoly(LVRef basicVar);
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

    std::vector<Polynomial<LVRef>::Term> tmp_storage;

    void ensureTableauReadyFor(LVRef v);

    void addRow(LVRef v, std::unique_ptr<Polynomial<LVRef>> p);
    std::unique_ptr<Polynomial<LVRef>> removeRow(LVRef v);
    void moveRowFromTo(LVRef from, LVRef to);
    void moveColFromTo(LVRef from, LVRef to);
    void addRowToColumn(LVRef row, LVRef col) { assert(cols[col.x]); cols[col.x]->addRow(row); }
    void removeRowFromColumn(LVRef row, LVRef col) { assert(cols[col.x]); cols[col.x]->removeRow(row); }
    void clearColumn(LVRef col) { assert(cols[col.x]); cols[col.x]->clear();}
    void normalizeRow(LVRef row);
};



#endif //OPENSMT_TABLEAU_H
