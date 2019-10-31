/*
Fast rationals
David Monniaux, VERIMAG 2008-2009

Copyright (c) 2008, 2009 Centre national de la recherche scientifique (CNRS)
 */
#include "FastRational.h"
#include <sstream>
#include <Sort.h>

//mpz_init(FastRational::one);
//mpz_set_si(FastRational::one, 1);
FastRational::FastRational( const char * s, const int base )
{
    mpq_init(mpq);
    mpq_set_str(mpq, s, base);
    mpq_canonicalize( mpq );
    state = State::MPQ_ALLOCATED_AND_VALID;
    try_fit_word();
    if ( wordPartValid() )
        kill_mpq( );
    assert( isWellFormed( ) );
}

FastRational::FastRational(uint32_t x)
{
    if (x > INT_MAX) {
        mpq_init(mpq);
        mpq_set_ui(mpq, x, 1);
        state = State::MPQ_ALLOCATED_AND_VALID;
    } else {
        num = x;
        den = 1;
        state = State::WORD_VALID;
    }
}

void FastRational::reset()
{
    kill_mpq(); state = State::WORD_VALID; num  = 0; den = 1;
}

void FastRational::print(std::ostream & out) const
{
//  const bool sign = num < 0;
    const bool sign = this->sign() < 0;
    if (wordPartValid()) {
        word abs_num = (sign?-num:num);
        if (den == 1) {
            out << (sign?"(- ":"") << abs_num << (sign?")":"");
        } else {
            out << "(/ " << (sign?"(- ":"") << abs_num << (sign?") ":" ") << den << ")";
        }
    } else {
        assert(mpqPartValid());
        mpq_class mpq_c( mpq );
        if ( sign ) mpq_c = -mpq_c;
        out << (sign?"(- ":"") << mpq_c << (sign?")":"");
    }
}

void FastRational::print_(std::ostream & out) const
{
    if (wordPartValid()) {
        if (den == 1) {
            out << num;
        } else {
            out << num << "/" << den;
        }
    } else {
        assert(mpqPartValid());
        out << mpq;
    }
}

std::string FastRational::get_str() const
{
    std::ostringstream os;
    print_(os);
    return os.str();
}

FastRational gcd(FastRational& a, FastRational& b)
{
    assert(a.isInteger() & b.isInteger());
    if (a.wordPartValid() && b.wordPartValid()) {
        return std::move(FastRational(gcd(a.num, b.num)));
    }
    else {
        a.ensure_mpq_valid();
        b.ensure_mpq_valid();
        mpz_t o;
        mpz_init(o);
        mpz_gcd(o, mpq_numref(a.mpq), mpq_numref(b.mpq));
        a.try_fit_word();
        b.try_fit_word();
        FastRational o_gcd = FastRational(mpz_class(o));
        mpz_clear(o);
        return std::move(o_gcd);
    }
}

FastRational lcm(FastRational& a, FastRational& b)
{
    assert(a.isInteger() & b.isInteger());
    if (a.wordPartValid() && b.wordPartValid()) {
        return std::move(lcm(a.num, b.num));
    }
    else {
        a.ensure_mpq_valid();
        b.ensure_mpq_valid();
        mpz_t o;
        mpz_init(o);
        mpz_lcm(o, mpq_numref(a.mpq), mpq_numref(b.mpq));
        if (!a.wordPartValid())
            a.try_fit_word();
        if (!b.wordPartValid())
            b.try_fit_word();
        FastRational o_gcd = FastRational(mpz_class(o));
        mpz_clear(o);
        return std::move(o_gcd);
    }
}

// The quotient of n and d using the fast rationals.
// Divide n by d, forming a quotient q.
// Rounds q down towards -infinity, and q will satisfy n = q*d + r for some 0 <= abs(r) <= abs(d)
// Don't care about converting n and d back to small values, since they're rvalues.
FastRational fastrat_fdiv_q(FastRational&& n, FastRational&& d) {
    assert(n.isInteger() && d.isInteger());
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

        return std::move(quo);
    }
overflow:
    n.force_ensure_mpq_valid();
    d.force_ensure_mpq_valid();
    mpz_t t;
    mpz_init(t);
    mpz_fdiv_q(t, mpq_numref(n.mpq), mpq_numref(d.mpq));
//    FastRational o = FastRational(mpz_class(t));
    return std::move(FastRational(mpz_class(t)));
}

FastRational fastrat_round_to_int(const FastRational& n) {
    FastRational res = n + FastRational(1, 2);
    return fastrat_fdiv_q(res.get_num(), res.get_den());
}

//  Same as above, but convert n and d to small values since they might have further use.
FastRational fastrat_fdiv_q(FastRational& n, FastRational& d) {
    assert(n.isInteger() && d.isInteger());
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

        return std::move(quo);
    }
    overflow:
    n.force_ensure_mpq_valid();
    d.force_ensure_mpq_valid();
    mpz_t t;
    mpz_init(t);
    mpz_fdiv_q(t, mpq_numref(n.mpq), mpq_numref(d.mpq));
//    FastRational o = FastRational(mpz_class(t));
    n.try_fit_word();
    d.try_fit_word();
    return std::move(FastRational(mpz_class(t)));
}

//void mpz_divexact (mpz_ptr, mpz_srcptr, mpz_srcptr);
FastRational divexact(FastRational& n, FastRational& d) {
    assert(d != 0);
    assert(n.isInteger() && d.isInteger());
    if (!n.mpqPartValid() && !d.mpqPartValid()) {
        word num = n.num;
        word den = d.num;
        word quo;
        if (den != 0){
            quo = num / den;
            return std::move(quo);
        }
        else {
            // Division by zero
            assert(false);
            return FastRational(0);
        }
    } else {
        assert(n.mpqPartValid() || d.mpqPartValid());
        n.force_ensure_mpq_valid();
        d.force_ensure_mpq_valid();
        mpz_t t;
        mpz_init(t);
        mpz_divexact(t, mpq_numref(n.mpq), mpq_numref(d.mpq));
        n.try_fit_word();
        d.try_fit_word();
        return std::move(FastRational(mpz_class(t)));
    }
}

// Given as input the sequence Reals, return the smallest number m such that for each r in Reals, r*m is an integer
FastRational get_multiplicand(const vec<FastRational>& reals)
{
    vec<FastRational> dens;
    for (int i = 0; i < reals.size(); i++)
        if (!reals[i].isInteger())
            dens.push_c(reals[i].get_den());

    // Iterate until dens is not empty
    FastRational mult = 1; // Collect here the number I need to multiply the polynomial to get rid of all denominators
    while (dens.size() > 0) {
        // Unique denominators
        sort(dens);
        uniq(dens);
#ifdef PRINTALOT
        char *buf = (char*) malloc(1);
        buf[0] = '\0';
        char *buf_new;

        for (int j = 0; j < dens.size(); j++) {
            asprintf(&buf_new, "%s%s%s", buf, dens[j].get_str().c_str(),
                     j == dens.size() - 1 ? "" : ", ");
            free(buf);
            buf = buf_new;
        }
        printf("Dens size now %lu, and individual are denominators: %s\n", dens.size(), buf);
        free(buf);
#endif
        if (dens.size() == 1) {
            mult *= dens[0];
            dens.clear();
        }
        else {
            // We filter in place the integers in dens.  The last two are guaranteed to be ;
            int k = 0;
            FastRational m = lcm(dens[dens.size()-1], dens[dens.size()-2]);
            mult *= m;
            for (int j = 0; j < dens.size()-2; j++) {
                FastRational n = (m/dens[j]).get_den();
                if (n != 1)
                    dens[k++] = n;
            }
            dens.resize(k);
        }
    }
#ifdef PRINTALOT
    printf("Multiplicand is %s\n", mult.get_str().c_str());
#endif
    return mult;
}
