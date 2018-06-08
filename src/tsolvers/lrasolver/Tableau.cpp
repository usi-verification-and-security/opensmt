//
// Created by Martin Blicha on 31.03.18.
//

#include "Tableau.h"
#include <iostream>

using namespace opensmt;
namespace {
    template<class C, class E>
    inline bool contains(const C & container, const E & elem){
        return container.find(elem) != container.end();
    }

    inline bool isOne(const opensmt::Real & r){
        return r == 1;
    }
}

void Tableau::nonbasicVar(LVRef v) {
    if(contains(cols, v)) {return;}
    assert(!contains(rows, v));
    newNonbasicVar(v);
}

void Tableau::newNonbasicVar(LVRef v) {
    if(contains(cols, v)){
        throw std::logic_error("Trying to insert the same variable more than once!");
    }
    cols[v]; // this deault-constructs the empty set for this variable
    nonbasic_vars.insert(v);
}

void Tableau::newBasicVar(LVRef v, Polynomial poly) {
    if(contains(rows, v)){
        throw std::logic_error("Trying to insert the same variable more than once!");
    }
    for(auto const & term : poly) {
        assert(contains(cols, term.first));
        cols.at(term.first).insert(v);
    }
    addRow(v, std::move(poly));
    basic_vars.insert(v);

}

std::size_t Tableau::getNumOfCols() const {
    return cols.size();
}

std::size_t Tableau::getPolySize(LVRef basicVar) const {
    assert(contains(rows, basicVar));
    return rows.at(basicVar).size();
}

const Polynomial & Tableau::getPoly(LVRef basicVar) const {
    assert(contains(rows, basicVar));
    return rows.at(basicVar);
}

Polynomial & Tableau::getPoly(LVRef basicVar) {
    assert(contains(rows, basicVar));
    return rows.at(basicVar);
}

const opensmt::Real & Tableau::getCoeff(LVRef basicVar, LVRef nonBasicVar) const {
    assert(contains(rows, basicVar));
    return rows.at(basicVar).getCoeff(nonBasicVar);
}

const Tableau::column_t & Tableau::getColumn(LVRef nonBasicVar) {
    assert(contains(cols, nonBasicVar));
    return cols.at(nonBasicVar);
}

const Tableau::rows_t & Tableau::getRows() const {
    return rows;
}

const Tableau::vars_t & Tableau::getNonBasicVars() const {
    return nonbasic_vars;
}

void Tableau::addRow(LVRef v, Polynomial p) {
    assert(!contains(rows, v));
    auto res = rows.emplace(v, std::move(p));
    assert(res.second);
    assert(!rows.empty());
}

void Tableau::removeRow(LVRef v) {
    assert(contains(rows, v));
    rows.erase(v);
}

bool Tableau::isProcessed(LVRef v) const {
    return contains(basic_vars, v) || contains(nonbasic_vars, v);
}

void Tableau::pivot(LVRef bv, LVRef nv) {
    //TODO: check if this method correctly updates column information
    // Take equation for bv and convert it to equation for nv
    // Substitute nv everywhere with its polynomial
    // Update column information: all (active) rows with nv now contains bv;
    // moreover some rows changes because of the substitution

    assert(isBasic(bv));
    assert(isNonBasic(nv));
    basic_vars.erase(bv);
    basic_vars.insert(nv);
    nonbasic_vars.erase(nv);
    nonbasic_vars.insert(bv);
    cols[bv];
    // compute the polynomial for nv
    assert(contains(rows, bv));
    Polynomial nvPoly = rows.at(bv);
    const auto coeff = nvPoly.getCoeff(nv);
    Real bvCoeff {1};
    if (!isOne(coeff)) {
        nvPoly.divideBy(coeff);
        bvCoeff /= coeff;
    }
    nvPoly.removeVar(nv);
    nvPoly.negate();
    nvPoly.addTerm(bv, bvCoeff);

    // remove row for bv, add row for nv
    removeRow(bv);
    addRow(nv, nvPoly);
    // update column information regarding this one poly
    for(auto & term : nvPoly) {
        auto var = term.first;
        if(var != bv) {
            auto erased = cols.at(var).erase(bv);
            assert(erased > 0);
        }
        assert(contains(cols, var));
        auto res = cols.at(var).insert(nv);
        assert(res.second);
    }

    // remove the bv row from nv column
    assert(contains(cols, nv));
    auto erased = cols.at(nv).erase(bv);
    assert(erased > 0);

    // for all (active) rows containing nv, substitute
    for (auto rowVar : getColumn(nv)) {
        if(!isActive(rowVar)) {
            continue;
        }
        // update the polynomials
        auto & poly = getPoly(rowVar);
        const auto& nvCoeff = poly.getCoeff(nv);
        auto changes = poly.merge(nvPoly, nvCoeff);
        poly.removeVar(nv);
        // update the column information
        assert(contains(cols, bv));
        assert(std::find(changes.added.begin(), changes.added.end(), bv) != changes.added.end());
        for (const auto & addedVar : changes.added) {
            assert(contains(cols, addedVar));
            assert(!contains(cols.at(addedVar), rowVar));
            cols.at(addedVar).insert(rowVar);
        }
        for (const auto & removedVar : changes.removed) {
            assert(contains(cols, removedVar));
            assert(contains(cols.at(removedVar), rowVar));
            cols.at(removedVar).erase(rowVar);
        }
    }
    assert(contains(cols, nv));
    cols.at(nv).clear();
}

void Tableau::clear() {
    this->rows.clear();
    this->cols.clear();
    this->basic_vars.clear();
    this->nonbasic_vars.clear();
}

bool Tableau::isActive(LVRef basicVar) const { return true;}

bool Tableau::isBasic(LVRef v) const {return contains(basic_vars, v);}
bool Tableau::isNonBasic(LVRef v) const {return contains(nonbasic_vars, v);}

void Tableau::print() const {
    std::cout << "Basic vars: ";
    for (auto var : basic_vars) {
        std::cout << var.x << " ";
    }
    std::cout << '\n';

    std::cout << "Non-basic vars: ";
    for (auto var : nonbasic_vars) {
        std::cout << var.x << " ";
    }
    std::cout << '\n';

    std::cout << "Rows:\n";
    for(auto row : rows) {
        std::cout << "Var of the row: " << row.first.x << ';';
        for (const auto & term : this->getPoly(row.first)) {
            std::cout << "( " << term.second << " | " << term.first.x << " ) ";
        }
        std::cout << '\n';
    }
    std::cout << '\n';
    std::cout << "Columns:\n";
    for(auto col : cols) {
        std::cout << "Var of the column: " << col.first.x << "; Contains: ";
        for (auto var : col.second) {
            std::cout << var.x << ' ';
        }
        std::cout << '\n';
    }
    std::cout << '\n';
}

bool Tableau::checkConsistency() const {
    bool res = true;
    for (auto nv : nonbasic_vars)  {
        res &= contains(cols, nv);
        assert(res);
    }
    for(auto const & col : cols) {
        auto var = col.first;
        if(col.second.empty()){
            // there could be empty non-basic variables; e.g. from atoms x <= 5
            // or here, we could have columns also or basic variables, which should be empty
            continue;
        }
        res &= contains(nonbasic_vars, var);
        assert(res);
        for(auto row : col.second) {
            res &= this->getPoly(row).contains(var);
            assert(res);
        }
    }

    for(auto const & row : rows) {
        auto var = row.first;
        if(!isActive(var)) {
            continue;
        }
        res &= contains(basic_vars, var);
        assert(res);
        for (auto const & term : row.second) {
            auto termVar = term.first;
            res &= contains(nonbasic_vars, termVar) && contains(cols, termVar);
            assert(res);
            res &= contains(cols.at(termVar), var);
            assert(res);
        }
    }
    return res;
}

std::vector<std::pair<LVRef, Polynomial>>
Tableau::doGaussianElimination(std::function<bool(LVRef)> shouldEliminate) {
//    print();
    assert(checkConsistency());
    std::vector<std::pair<LVRef, Polynomial>> removed;
    auto old_nonbasic_vars = nonbasic_vars;
    for (auto var : old_nonbasic_vars) {
        assert(contains(cols, var));
        auto col_it = cols.find(var);
        if (!shouldEliminate(var) || col_it == cols.end() || col_it->second.empty()) { continue; }
        // we are going to eliminate this column variable from the tableau
        // pick row which we are going to use to express this variable
        auto const & col = *col_it;
        auto const & col_rows = col.second;
        LVRef chosen_row = *(col_rows.begin());
        auto min_size = rows.at(chosen_row).size();
        for (auto it = ++col_rows.begin(); it != col_rows.end(); ++it) {
            auto size = rows.at(*it).size();
            if (size < min_size) {
                min_size = size;
                chosen_row = *it;
            }
        }
        // remember the original polynomial
        Polynomial poly = rows.at(chosen_row);
        // remove the row completly, update the column information; TODO: this can be done together in one method
        removeRow(chosen_row);
        for (auto const & term : poly) {
            auto l_var = term.first;
            assert(contains(cols, l_var));
            cols.at(l_var).erase(chosen_row);
        }
        assert(contains(basic_vars, chosen_row));
        basic_vars.erase(chosen_row);
        nonbasic_vars.insert(chosen_row);
        cols[chosen_row];
        // now express the chosen_row in terms of column variable
        {
            auto coeff = poly.getCoeff(var);
            coeff.negate();
            poly.removeVar(var);
            poly.addTerm(chosen_row, -1);
            poly.divideBy(coeff);
        }
        // remember the polynomial for removed var
        removed.emplace_back(var, poly);
        // now substitute in other rows where var is present
        for (auto rowVar : col_rows) {
            if (rowVar == chosen_row) { continue; }
            assert(rows.find(rowVar) != rows.end());
            auto & row_poly = rows.at(rowVar);
            auto coeff = row_poly.getCoeff(var);
            row_poly.removeVar(var);
            auto res = row_poly.merge(poly, coeff);
            // process added and removed vars
            // TODO: unite the operation done here an during pivoting
            for (const auto & addedVar : res.added) {
                assert(contains(cols, addedVar));
                assert(!contains(cols.at(addedVar), rowVar));
                cols.at(addedVar).insert(rowVar);
            }
            for (const auto & removedVar : res.removed) {
                assert(contains(cols, removedVar));
                assert(contains(cols.at(removedVar), rowVar));
                cols.at(removedVar).erase(rowVar);
            }
        }
        // remove the eliminated column
        assert(contains(nonbasic_vars, var));
        nonbasic_vars.erase(var);
        assert(contains(cols, var));
        cols.erase(var);
//        print();
    }
    assert(checkConsistency());
    return removed;
}