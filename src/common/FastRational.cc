/*
Fast rationals
David Monniaux, VERIMAG 2008-2009

Copyright (c) 2008, 2009 Centre national de la recherche scientifique (CNRS)
 */

#include "FastRational.h"
#include "FastInteger.h"

#include <sstream>
#include <algorithm>

namespace opensmt {

mpq_ptr FastRational::mpqPool::alloc()
{
    mpq_ptr r;
    if (!pool.empty()) {
        r = pool.top();
        pool.pop();
    } else {
        r = store.emplace().get_mpq_t();
    }
    return r;
}

void FastRational::mpqPool::release(mpq_ptr ptr)
{
    pool.push(ptr);
}

FastRational::FastRational( const char * s, const int base )
{
    mpq = pool.alloc();
    mpq_set_str(mpq, s, base);
    mpq_canonicalize( mpq );
    state = State::MPQ_ALLOCATED_AND_VALID;
    try_fit_word();
    if ( wordPartValid() )
        kill_mpq( );
    assert( isWellFormed( ) );
}

FastRational::FastRational(mpz_t z)
{
    if (mpz_fits_sint_p(z)) {
        num = mpz_get_si(z);
        den = 1;
        state = State::WORD_VALID;
    } else {
        mpq = pool.alloc();
        mpz_set(mpq_numref(mpq), z);
        mpz_set_ui(mpq_denref(mpq), 1);
        state = State::MPQ_ALLOCATED_AND_VALID;
    }
}

FastRational::FastRational(uint32_t x)
{
    if (x > INT_MAX) {
        mpq = pool.alloc();
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
    const bool sign = this->sign() < 0;
    if (wordPartValid()) {
        uword abs_num = absVal(num);
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

FastRational fastrat_round_to_int(const FastRational& n) {
    FastRational res = n + FastRational(1, 2);
    return fastint_fdiv_q(static_cast<FastInteger&&>(res.get_num()), static_cast<FastInteger&&>(res.get_den()));
}

// Given as input the sequence Reals, return the smallest number m such that for each r in Reals, r*m is an integer
FastRational get_multiplicand(const std::vector<FastRational>& reals)
{
    std::vector<FastRational> dens;
    for (const auto & r : reals) {
        if (!r.isInteger()) {
            dens.push_back(r.get_den());
        }
    }

    // Iterate until dens is not empty
    FastRational mult = 1; // Collect here the number I need to multiply the polynomial to get rid of all denominators
    while (dens.size() > 0) {
        // Unique denominators
        std::sort(dens.begin(), dens.end());
        auto last = std::unique(dens.begin(), dens.end());
        dens.erase(last, dens.end());
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
            FastRational m = lcm(static_cast<FastInteger&>(dens[dens.size()-1]), static_cast<FastInteger&>(dens[dens.size()-2]));
            mult *= m;
            for (size_t j = 0; j < dens.size()-2; j++) {
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

}
