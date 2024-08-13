/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>
        Aliaksei Tsitovich <aliaksei.tsitovich@gmail.com>

OpenSMT2 -- copyright (C) 2012 - 2015, Antti Hyvarinen
OpenSMT -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#include "LA.h"

#include <iostream>

namespace opensmt {

void LAExpression::initialize(PTRef e, bool do_canonize) {
    assert(logic.isNumEq(e) || logic.isLeq(e));

    PTRef lhs = logic.getPterm(e)[0];
    PTRef rhs = logic.getPterm(e)[1];
    std::vector<PTRef> curr_term{lhs, rhs};
    std::vector<Real> curr_const{1, -1};

    while (!curr_term.empty()) {
        PTRef t = curr_term.back();
        assert(logic.yieldsSortNum(t));
        curr_term.pop_back();
        Real c = curr_const.back();
        curr_const.pop_back();
        // Only 3 cases are allowed
        //
        // If it is plus, enqueue the arguments with same constant
        if (logic.isPlus(t)) {
            const Pterm & term = logic.getPterm(t);
            for (PTRef arg : term) {
                curr_term.emplace_back(arg);
                curr_const.emplace_back(c);
            }
        } else if (logic.isTimes(t)) {
            // If it is times, then one side must be constant, other
            // is enqueued with a new constant
            auto [var, constant] = logic.splitTermToVarAndConst(t);
            Real new_c = logic.getNumConst(constant);
            new_c *= c;
            curr_term.emplace_back(var);
            curr_const.emplace_back(std::move(new_c));
        } else {
            // Otherwise it is a variable, Ite, UF or constant
            assert(logic.isNumVarLike(t) || logic.isConstant(t) || logic.isUF(t));
            if (logic.isConstant(t)) {
                const Real tval = logic.getNumConst(t);
                polynome[PTRef_Undef] += tval * c;
            } else {
                auto it = polynome.find(t);
                if (it != polynome.end()) {
                    it->second += c;
                    if (it->first != PTRef_Undef && it->second == 0)
                        polynome.erase(it);
                } else {
                    polynome.insert({t, c});
                }
            }
        }
    }

    if (polynome.find(PTRef_Undef) == polynome.end()) {
        polynome.insert({PTRef_Undef, 0});
    }
    //
    // Canonize
    //
    if (do_canonize) {
        canonize();
    }
}

PTRef LAExpression::toPTRef(SRef sort) const {
    assert(polynome.find(PTRef_Undef) != polynome.end());
    assert(not polynome.empty());
    //
    // There is at least one variable
    //
    vec<PTRef> sum_list;
    Real constant = 0;
    for (auto const & [var, factor] : polynome) {
        if (var == PTRef_Undef) {
            constant = factor;
        } else {
            PTRef coeff = logic.mkConst(sort, factor);
            sum_list.push(logic.mkTimes(coeff, var));
        }
    }
    if (sum_list.size() == 0) {
        sum_list.push(logic.getZeroForSort(sort));
    }
    // Return in the form ax + by + ... = -c
    if (r == OP::EQ || r == OP::LEQ) {
        PTRef poly = logic.mkPlus(sum_list);
        constant.negate();
        PTRef c = logic.mkConst(sort, constant);
        if (r == OP::EQ) {
            return logic.mkEq(poly, c);
        } else {
            return logic.mkLeq(poly, c);
        }
    }
    // Return in the form ax + by + ... + c
    assert(r == OP::UNDEF);
    sum_list.push(logic.mkConst(sort, constant));
    PTRef poly = logic.mkPlus(sum_list);
    return poly;
}

void LAExpression::print(std::ostream & os) const {
    assert(polynome.find(PTRef_Undef) != polynome.end());
    assert(not polynome.empty());
    if (r == OP::EQ)
        os << "(=";
    else if (r == OP::LEQ)
        os << "(<=";
    Real constant = 0;
    if (polynome.size() == 1)
        os << " " << polynome.at(PTRef_Undef);
    else {
        // There is at least one variable
        os << " (+";
        for (auto const & [var, factor] : polynome) {
            if (var == PTRef_Undef)
                constant = - factor;
            else
                os << " (* " << factor << " " << logic.printTerm(var) << ")";
        }
        os << ")";
    }
    if (r == OP::EQ || r == OP::LEQ)
        os << " " << constant << ")";
    os << '\n';
}

opensmt::pair<PTRef, PTRef> LAExpression::getSubst() {
    if (polynome.size() == 1) {
        assert(polynome.find(PTRef_Undef) != polynome.end());
        return {PTRef_Undef, PTRef_Undef};
    }
    // There is at least one variable
    // Solve w.r.t. first variable
    solve();
    vec<PTRef> sum_list;
    Real constant = 0;
    PTRef var = PTRef_Undef;
    SRef polySort = SRef_Undef;
    for (auto const & [v, factor] : polynome) {
        if (v == PTRef_Undef) {
            constant = - factor;
        } else {
            polySort = polySort != SRef_Undef ? polySort : logic.getSortRef(v);
            if (var == PTRef_Undef) {
                var = v;
                assert(factor == 1);
            } else {
                PTRef c =  logic.mkConst(polySort, - factor);
                sum_list.push(logic.mkTimes(c, v));
            }
        }
    }
    assert(polySort != SRef_Undef);
    sum_list.push(logic.mkConst(polySort, constant));
    PTRef poly = logic.mkPlus(sum_list);
    return {var, poly};
}

//
// Solve w.r.t. first variable
// ex.
//
// 3*x + 2*y -1*z + 5 = 0
//
// 1*x + 2/3*y - 1/3*z + 5/3 = 0
//
// it modifies the polynome internally
//
PTRef LAExpression::solve() {
    assert(r == OP::EQ);
    assert(polynome.find(PTRef_Undef) != polynome.end());
    if (polynome.size() == 1) {
        assert(polynome.find(PTRef_Undef) != polynome.end());
        return PTRef_Undef;
    }
    //
    // Get first useful variable
    //
    auto it = polynome.begin();
    if (it->first == PTRef_Undef) it++;
    PTRef var = it->first;
    const Real coeff = it->second;
    //
    // Divide polynome by coeff
    //
    for (auto & term: polynome) {
        term.second /= coeff;
    }
    assert(polynome[var] == 1);
    return var;
}

//
// Canonize w.r.t. first variable
// ex.
//
// 3*x + 2*y -1*z + 5 = 0
//
// 1*x + 2/3*y - 1/3*z + 5/3 = 0
//
// it modifies the polynome internally
//
void
LAExpression::canonize() {
    if (polynome.size() == 1) {
        assert(polynome.find(PTRef_Undef) != polynome.end());
        return;
    }
    // Get first useful variable
    auto it = polynome.begin();
    if (it->first == PTRef_Undef) it++;
    if (r == OP::LEQ) {
        const Real abs_coeff = (it->second > 0 ? it->second : Real(-it->second));
        for (auto & term: polynome) {
            term.second /= abs_coeff;
        }
    } else {
        const Real coeff = it->second;
        for (auto & term: polynome) {
            term.second /= coeff;
        }
    }
    assert(isCanonized());
}

void LAExpression::addExprWithCoeff(const LAExpression & a, const Real & coeff) {
    //
    // Iterate over expression to add
    //
    for (auto const & [var, factor] : a.polynome) {
        assert(var == PTRef_Undef or logic.yieldsSortNum(var));
        auto it2 = polynome.find(var);
        if (it2 != polynome.end()) {
            it2->second += coeff * factor;
            if (it2->first != PTRef_Undef && it2->second == 0)
                polynome.erase(it2);
        } else {
            polynome.insert({var, coeff * factor});
        }
    }
}

}
