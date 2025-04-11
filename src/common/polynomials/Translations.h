/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_TRANSLATIONS_H
#define OPENSMT_TRANSLATIONS_H

#include "Polynomial.h"

#include <logics/ArithLogic.h>
#include <pterms/PTRef.h>

namespace opensmt {

using LAPoly = PolynomialT<PTRef>;

/// Given an (in)equality @p op of the form "lhs op ths", returns a polynomial p such that p := rhs - lhs
LAPoly ptrefToPoly(PTRef op, ArithLogic & logic);

/// Given a polynomial, returns its representation as a pterm.
/// If the expected @p type is integer, the polynomial is first normalized if needed,
/// i.e, multiplied by a constant to ensure no fractional coefficients.
PTRef polyToPTRef(LAPoly & poly, ArithLogic & logic, SRef type);

} // namespace opensmt

#endif // OPENSMT_TRANSLATIONS_H
