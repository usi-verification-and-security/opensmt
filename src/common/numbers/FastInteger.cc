#include "FastInteger.h"

namespace opensmt {
FastInteger::FastInteger(const char* str, const int base) : FastRational(str, base) {
    assert(isIntegerValue());
}

FastInteger gcd(FastInteger const & a, FastInteger const & b)
{
    assert(a.isIntegerValue() and b.isIntegerValue());
    if (a.wordPartValid() && b.wordPartValid()) {
        // Refers to FastRational.h:gcd
        return FastInteger(gcd(a.num, b.num));
    }
    else {
        a.ensure_mpq_valid();
        b.ensure_mpq_valid();
        mpz_gcd(FastInteger::mpz(), mpq_numref(a.mpq), mpq_numref(b.mpq));
        return FastInteger(FastInteger::mpz());
    }
}

FastInteger lcm(FastInteger const & a, FastInteger const & b)
{
    assert(a.isIntegerValue() and b.isIntegerValue());
    if (a.wordPartValid() && b.wordPartValid()) {
        // Refers to FastRational.h:lcm
        return lcm(a.num, b.num);
    }
    else {
        a.ensure_mpq_valid();
        b.ensure_mpq_valid();
        mpz_lcm(FastInteger::mpz(), mpq_numref(a.mpq), mpq_numref(b.mpq));
        return FastInteger(FastInteger::mpz());
    }
}

// The quotient of n and d using the fast rationals.
// Divide n by d, forming a quotient q.
// Rounds q down towards -infinity, and q will satisfy n = q*d + r for some 0 <= abs(r) <= abs(d)
FastInteger fastint_fdiv_q(FastInteger const & n, FastInteger const & d) {
    assert(n.isIntegerValue() && d.isIntegerValue());
    if (n.wordPartValid() && d.wordPartValid()) {
        word num = n.num;
        word den = d.num;
        word quo;
        if (num == INT_MIN) // The abs is guaranteed to overflow.  Otherwise this is always fine
            goto overflow;
        // After this -INT_MIN+1 <= numerator <= INT_MAX, and therefore the result always fits into a word.
        quo = num / den;
        if (num % den != 0 && ((num < 0 && den >=0) || (den < 0 && num >= 0))) // The result should be negative
            quo--; // INT_MAX-1 >= quo >= -INT_MIN

        return quo;
    }
overflow:
    n.ensure_mpq_valid();
    d.ensure_mpq_valid();
    mpz_fdiv_q(FastInteger::mpz(), mpq_numref(n.mpq), mpq_numref(d.mpq));
    return FastInteger(FastInteger::mpz());
}

//void mpz_divexact (mpz_ptr, mpz_srcptr, mpz_srcptr);
FastInteger divexact(FastInteger const & n, FastInteger const & d) {
    assert(d != 0);
    assert(n.isIntegerValue() && d.isIntegerValue());
    if (n.wordPartValid() && d.wordPartValid()) {
        word num = n.num;
        word den = d.num;
        word quo;
        if (den != 0){
            quo = num / den;
            return quo;
        }
        else {
            // Division by zero
            assert(false);
            return FastInteger(0);
        }
    } else {
        assert(n.mpqPartValid() || d.mpqPartValid());
        n.ensure_mpq_valid();
        d.ensure_mpq_valid();
        mpz_divexact(FastInteger::mpz(), mpq_numref(n.mpq), mpq_numref(d.mpq));
        return FastInteger(FastInteger::mpz());
    }
}
}
