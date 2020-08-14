/*
Fast rationals
David Monniaux, VERIMAG 2008-2009

Copyright (c) 2008, 2009 Centre national de la recherche scientifique (CNRS)
 */
#ifndef FAST_RATIONALS_H
#define FAST_RATIONALS_H
#include <string>
#include <gmpxx.h>
#include <cassert>
#include <climits>
#include "Vec.h"

typedef int32_t  word;
typedef uint32_t uword;
typedef int64_t  lword;
typedef uint64_t ulword;
#define WORD_MIN  INT_MIN
#define WORD_MAX  INT_MAX
#define UWORD_MAX UINT_MAX
#define LWORD_MIN LONG_MIN
#define LWORD_MAX LONG_MAX

class MpzUnit
{
private:
    mpz_t unit;
public:
    MpzUnit() { mpz_init(unit); mpz_set_si(unit, 1); }
    const mpz_t& getUnit() const { return unit; }
};

enum class State: unsigned char {
    /*
     * bit 0 - wheter word part is valid or not
     * bit 1 - whether memory for mpq has been allocated
     * bit 2 - whether mpq part is valid
     *
     * INVARIANT - if both parts are valid, they are the same
     */

    WORD_VALID = 1, // ONLY the WORD part is valid and memory for MPQ is not initialized
    MPQ_MEMORY_ALLOCATED = 2, // SHOULD NEVER BE STANDALONE
    WORD_PLUS_MPQ_INITIALIZED = WORD_VALID | MPQ_MEMORY_ALLOCATED, // ONLY the WORD part is valid, but memory is already initialized
    MPQ_VALID = 4, // // SHOULD NEVER BE STANDALONE
    MPQ_ALLOCATED_AND_VALID = MPQ_MEMORY_ALLOCATED | MPQ_VALID, // ONLY MPQ part is valid
    WORD_AND_MPQ = WORD_VALID | MPQ_ALLOCATED_AND_VALID // BOTH WORD and MPQ parts are valid (and they are the same)
};

using state_t = std::underlying_type<State>::type;
static_assert(std::is_same<state_t,unsigned char>::value, "Underlying value for FastRational inner type is not as expected");

inline State operator | (State lhs, State rhs)
{
    return static_cast<State>(static_cast<state_t>(lhs) | static_cast<state_t>(rhs));
}

inline State& operator |= (State& lhs, State rhs)
{
    lhs = lhs | rhs;
    return lhs;
}

inline uword absVal(word x) {
    // Taking just (- WORD_MIN) is undefined behaviour, changed according to https://stackoverflow.com/questions/12231560/correct-way-to-take-absolute-value-of-int-min
    return x < 0 ? -((uword)(x))
                 : +((uword)(x));
}

inline ulword absVal(lword x) {
    // Taking just (- LWORD_MIN) is undefined behaviour
    return x < 0 ? -((ulword)(x))
                 : +((ulword)(x));
}

class FastRational
{
    static const MpzUnit unit;

    // Bit masks for questioning state:
    static const unsigned char wordValidMask = 0x1;
    static const unsigned char mpqMemoryAllocatedMask = 0x2;
    static const unsigned char mpqValidMask = 0x4;

    // Methods for adjusting the inner state
    inline void setMpqPartValid() {this->state |= State::MPQ_VALID; }
    inline void setMpqMemoryAllocated() {this->state |= State::MPQ_MEMORY_ALLOCATED; }
    inline void setMpqAllocatedAndValid() {this->state |= State::MPQ_ALLOCATED_AND_VALID; }
    inline void setWordPartValid() {this->state |= State::WORD_VALID; }
    inline void setWordPartInvalid() { assert(mpqPartValid()); this->state = State::MPQ_ALLOCATED_AND_VALID; }

    void setMpqPartInvalid() {
        assert(wordPartValid());
        // TODO: improve
        if (this->mpqMemoryAllocated()) { state = State::WORD_PLUS_MPQ_INITIALIZED; }
        else {
            state = State::WORD_VALID;
        }
    }
public:
    // Methods for questioning inner state
    inline bool wordPartValid() const { return  static_cast<state_t>(state) & wordValidMask; }
    inline bool mpqMemoryAllocated() const { return  static_cast<state_t>(state) & mpqMemoryAllocatedMask; }
    inline bool mpqPartValid() const { return  static_cast<state_t>(state) & mpqValidMask; }

    //
    // Constructors
    //
    FastRational( ) : state{State::WORD_VALID}, num(0), den(1) { }
    FastRational( word x ) : state{State::WORD_VALID}, num(x), den(1) { }
    FastRational(uint32_t);
    inline FastRational(word n, uword d);
    explicit FastRational(const char* s, const int base = 10);
    inline FastRational( const FastRational & );
    inline FastRational(FastRational&& other) noexcept;
    FastRational & operator=(FastRational && other) {
        std::swap(this->state, other.state);
        std::swap(this->num, other.num);
        std::swap(this->den, other.den);
        std::swap(this->mpq, other.mpq);
        return *this;
    }

    FastRational( const mpz_class & x )
    {
        if ( x.fits_sint_p() ) {
            num = x.get_si();
            den = 1;
            state = State::WORD_VALID;
        }
        else {
            mpq_init( mpq );
            mpq_set_num( mpq, x.get_mpz_t( ) );
            mpz_class tmp_den = 1;
            mpq_set_den( mpq, tmp_den.get_mpz_t( ) );
            state = State::MPQ_ALLOCATED_AND_VALID;
        }
    }
    //
    // Destroyer
    //
    ~FastRational( ) { kill_mpq(); }
    void reset();
    inline FastRational & operator=( const FastRational & );
private:
    void kill_mpq()
    {
        if (mpqMemoryAllocated()) {
            mpq_clear(mpq);
            state = State::WORD_VALID;
        }
    }
    void ensure_mpq_valid() {
        if (!mpqPartValid()) {
            assert(wordPartValid());
            if (!mpqMemoryAllocated()) {
                mpq_init(mpq);
            }
            mpz_set_si(mpq_numref(mpq), num);
            mpz_set_ui(mpq_denref(mpq), den);
            setMpqAllocatedAndValid();
        }
    }
    void force_ensure_mpq_valid() const
    {
        const_cast<FastRational *>(this)->ensure_mpq_valid();
    }
    void ensure_mpq_memory_allocated()
    {
        if (!mpqMemoryAllocated()) {
            mpq_init(mpq);
            setMpqMemoryAllocated();
        }
    }
    //
    // Tries to convert the current rational
    // stored in mpq into word/uword
    //
    void try_fit_word()
    {
        assert( mpqPartValid() );
        assert(!wordPartValid()); // MB: It does not make sense to call this method if word is valid
        if ( mpz_fits_sint_p(mpq_numref(mpq))
             && mpz_fits_uint_p(mpq_denref(mpq))) {
            num = mpz_get_si(mpq_numref(mpq));
            den = mpz_get_ui(mpq_denref(mpq));
            setWordPartValid();
        }
    }
    friend inline void addition            ( FastRational &, const FastRational &, const FastRational & );
    friend inline void substraction         ( FastRational &, const FastRational &, const FastRational & );
    friend inline void multiplication      ( FastRational &, const FastRational &, const FastRational & );
    friend inline void division            ( FastRational &, const FastRational &, const FastRational & );
    friend inline void additionAssign      ( FastRational &, const FastRational & );
    friend inline void substractionAssign   ( FastRational &, const FastRational & );
    friend inline void multiplicationAssign( FastRational &, const FastRational & );
    friend inline void divisionAssign      ( FastRational &, const FastRational & );
    friend FastRational gcd(FastRational&, FastRational&);
    friend FastRational lcm(FastRational&, FastRational&);
    friend FastRational fastrat_fdiv_q(FastRational& n, FastRational& d);
    friend FastRational fastrat_fdiv_q(FastRational&& n, FastRational&& d);
    friend FastRational divexact(FastRational& n, FastRational& d);
public:
    void print_details ( std::ostream & ) const;
    void print         ( std::ostream & ) const;
    inline double get_d  ( ) const;
    std::string   get_str( ) const;
    inline bool operator==(const FastRational& b) const;
    inline FastRational operator-() const;
    inline void negate();
private:
    void print_(std::ostream& out) const;
    static inline int compare(lword a, lword b) {
        if (a < b) return -1;
        else if (a > b) return 1;
        else return 0;
    }
//    bool has_mpq, has_word;
    State state;
    word num;
    uword den;
    mpq_t mpq;
public:
    FastRational get_den() const {
        if (wordPartValid() && den <= INT32_MAX)
            return (uword)den;
        else
            return FastRational(mpz_class(mpq_denref(mpq)));
    }
    FastRational get_num() const {
        if (wordPartValid())
            return num;
        else
            return FastRational(mpz_class(mpq_numref(mpq)));
    }

    inline int compare(const FastRational& b) const;
    inline int sign() const;
    bool operator< ( const FastRational & b ) const { return compare(b) < 0; }
    bool operator> ( const FastRational & b ) const { return compare(b) > 0; }
    bool operator<=( const FastRational & b ) const { return compare(b) <= 0; }
    bool operator>=( const FastRational & b ) const { return compare(b) >= 0; }
    bool operator!=( const FastRational & b ) const { return !(*this == b); }
    inline unsigned size() const;

    uint32_t getHashValue() const {
        if  (wordPartValid()) {
            return 37*(uint32_t)num + 13*(uint32_t)den;
        }
        else {
            uint32_t h_n = 2166136261U;
            for (int i = 0; i < mpq->_mp_num._mp_size; i++) {
                h_n *= 16777619U;
                h_n ^=  mpq->_mp_num._mp_d[i];
            }
            uint32_t h_d = 2166136261U;
            for (int i = 0; i < mpq->_mp_den._mp_size; i++) {
                h_d *= 16777619U;
                h_d ^=  mpq->_mp_den._mp_d[i];
            }
            return h_n + h_d;
        }
    }

    bool isInteger() const {
        if (wordPartValid())
            return den == 1;
        else {
            assert(mpqPartValid());
            return mpz_fits_uint_p(mpq_denref(mpq)) && (mpz_get_ui(mpq_denref(mpq)) == 1);
        }
    }
    inline FastRational ceil( ) const
    {
        if (isInteger())
            return *this;

        if (wordPartValid()) {
            word ret = (num > 0 ? (uword)num : (uword)(-num) ) / den;
            if ( num < 0 ) ret = -ret;
            else ++ret;
            return ret;
        }
        else {
            mpz_class q;
            mpz_cdiv_q (q.get_mpz_t() , mpq_numref(mpq) , mpq_denref(mpq));
            FastRational ret( q );
            return ret;
        }
    }
    inline FastRational floor( ) const
    {
        if (isInteger()) return *this;
        return ceil( ) - 1;
    }
    bool isWellFormed() const;
    FastRational operator+(const FastRational& b) const
    {
        FastRational dest;
        assert(isWellFormed());
        assert(b.isWellFormed());
        addition(dest, *this, b);
        assert(dest.isWellFormed());
        return dest;
    }
    FastRational operator-(const FastRational& b) const
    {
        FastRational dest;
        assert(isWellFormed());
        assert(b.isWellFormed());
        substraction(dest, *this, b);
        assert(dest.isWellFormed());
        return dest;
    }
    FastRational operator*(const FastRational& b) const
    {
        FastRational dest;
        assert(isWellFormed());
        assert(b.isWellFormed());
        multiplication(dest, *this, b);
        assert(dest.isWellFormed());
        return dest;
    }
    FastRational operator/(const FastRational& b) const
    {
        FastRational dest;
        assert(isWellFormed());
        assert(b.isWellFormed());
        division(dest, *this, b);
        assert(dest.isWellFormed());
        return dest;
    }
    FastRational& operator+=(const FastRational& b)
    {
        assert(isWellFormed());
        assert(b.isWellFormed());
        additionAssign(*this, b);
        assert(isWellFormed());
        return *this;
    }
    FastRational& operator-=(const FastRational& b)
    {
        assert(isWellFormed());
        assert(b.isWellFormed());
        substractionAssign(*this, b);
        assert(isWellFormed());
        return *this;
    }
    FastRational& operator*=(const FastRational& b)
    {
        assert(isWellFormed());
        assert(b.isWellFormed());
        multiplicationAssign(*this, b);
        assert(isWellFormed());
        return *this;
    }
    FastRational& operator/=(const FastRational& b)
    {
        assert(isWellFormed());
        assert(b.isWellFormed());
        divisionAssign(*this, b);
        assert(isWellFormed());
        return *this;
    }
    inline FastRational inverse() const;
    bool isZero() const {
        if (wordPartValid()) {
            return num==0;
        } else {
            return mpq_sgn(mpq)==0;
        }
    }


    // Return *this % d.  The return value will have the sign of d
    FastRational operator%(const FastRational& d) {
        assert(isInteger() && d.isInteger());
        if (!mpqPartValid() && !d.mpqPartValid()) {
            lword w = absVal(num % d.num);
            return (word)(d.num > 0 ? w : -w);
        }
        FastRational r = (*this) / d;
        r = r.floor();
        r = (*this) - r*d;
        return r;
    }
};
// Divide n by d, forming a quotient q.
// Rounds q down towards -infinity, and r will have the same sign as d.
FastRational fastrat_fdiv_q(FastRational&& n, FastRational&& d);
FastRational fastrat_fdiv_q(FastRational& n, FastRational& d);
FastRational fastrat_round_to_int(const FastRational& n);

FastRational gcd(FastRational& a, FastRational& b);

FastRational lcm(FastRational& a, FastRational& b);

struct FastRationalHash {
    uint32_t operator() (const FastRational& s) const {
        return (uint32_t)s.getHashValue();
    }
};

inline std::ostream & operator<<(std::ostream & out, const FastRational & r)
{
    r.print(out);
    return out;
}
inline FastRational::FastRational(const FastRational& x) {
    if (x.wordPartValid()) {
        num = x.num;
        den = x.den;
        state = State::WORD_VALID;
    }
    else {
        assert(x.mpqPartValid());
        mpq_init(mpq);
        mpq_set(mpq, x.mpq);
        state = State::MPQ_ALLOCATED_AND_VALID;
    }
}

inline FastRational::FastRational(FastRational &&other) noexcept : state{other.state}, num{other.num}, den{other.den}  {
    if (other.mpqMemoryAllocated()) {
        std::swap(this->mpq, other.mpq);
        other.state = State::WORD_VALID;
    }
}

inline FastRational& FastRational::operator=(const FastRational& x) {
    if (x.wordPartValid()) {
        num = x.num;
        den = x.den;
        setWordPartValid();
        setMpqPartInvalid(); // MB: keeps mpq memory allocated if it already is
    }
    else {
        assert(x.mpqPartValid());
        if (!this->mpqMemoryAllocated()) {
            mpq_init(mpq);
        }
        mpq_set(mpq, x.mpq);
        this->state = State::MPQ_ALLOCATED_AND_VALID;
    }
    return *this;
}

inline bool FastRational::operator==(const FastRational& b) const {
    if (this->wordPartValid() && b.wordPartValid()) {
        return num == b.num && den == b.den;
    }
    force_ensure_mpq_valid();
    b.force_ensure_mpq_valid();
    return mpq_equal(mpq, b.mpq);
}

inline FastRational FastRational::operator-() const {
    if (this->wordPartValid() && num > WORD_MIN) {
        return FastRational(-num, den);
    } else {
        force_ensure_mpq_valid();
        FastRational x;
        mpq_init(x.mpq);
        mpq_neg(x.mpq, mpq);
        x.state = State::MPQ_ALLOCATED_AND_VALID;
        return x;
    }
}

inline void FastRational::negate() {
    if (this->wordPartValid() && num > WORD_MIN) {
        num = -num;
        setMpqPartInvalid();
    } else {
        force_ensure_mpq_valid();
        mpq_neg(mpq, mpq);
        // MB: for the special case num == WORD_MIN && wordPartValid
        setWordPartInvalid();
    }
}

inline int FastRational::compare(const FastRational& b) const {
    if (this->wordPartValid() && b.wordPartValid()) {
        if (b.den == den) {
            return compare(num, b.num);
        } else {
            return compare(lword(num)*b.den, lword(b.num)*den);
        }
    }
    force_ensure_mpq_valid();
    b.force_ensure_mpq_valid();
    return mpq_cmp(mpq, b.mpq);
}

inline int FastRational::sign() const {
    if (wordPartValid()) {
        if (num < 0) return -1;
        else if (num > 0) return 1;
        else return 0;
    } else {
        assert(mpqPartValid());
        return mpq_sgn(mpq);
    }
}

template<typename integer> integer gcd(integer a, integer b) {
    if (a==0) return b;
    if (b==0) return a;
    if (b > a) {
        integer c = a;
        a = b;
        b = c;
    }
    while(true) {
        integer r = a%b;
        if (r==0) return b;
        a = b;
        b = r;
    }
}

template<typename integer>
FastRational lcm(integer a, integer b) {
    if (a == 0) return 0;
    if (b == 0) return 0;
    if (b > a)
        return FastRational(b / gcd(a, b)) * a;
    else
        return FastRational(a / gcd(a, b)) * b;
}

// Return 1 if |op1| > |op2|, -1 if |op1| < |op2|, and 0 if op1 = op2
inline int cmpabs(FastRational op1, FastRational op2)
{
    if (op1.sign() == -1)
        op1 = -op1;
    if (op2.sign() == -1)
        op2 = -op2;
    return op1.compare(op2);
};
template<ulword> ulword gcd(ulword a, ulword b);
template<uword> uword gcd(uword a, uword b);
#define CHECK_WORD(var, value) \
    do { \
        lword tmp = value; \
        if (tmp < WORD_MIN/2 || tmp > WORD_MAX/2) { \
            goto overflow; \
        } \
        var = tmp;\
    } while(0)
#define CHECK_SUM_OVERFLOWS_LWORD(var, s1, s2) \
    do { \
        if ((s1 > LWORD_MAX/2 || s2 > LWORD_MAX/2) || (s1 < LWORD_MIN/2 || s2 < LWORD_MIN/2)) { \
            goto overflow; \
        } \
        var = s1 + s2;\
    } while(0)
#define CHECK_POSITIVE(value) \
    if (value < 1) abort()
#define CHECK_UWORD(var, value) \
    do { \
        CHECK_POSITIVE(value); \
        ulword tmp = value; \
        if (tmp > UWORD_MAX) { \
            goto overflow; \
        } \
        var = tmp;\
    } while(0)
#define COMPUTE_WORD(var, value) \
    word var; CHECK_WORD(var, value)

inline bool FastRational::isWellFormed() const
{
    return (  wordPartValid() || mpqPartValid() )
           && ( !wordPartValid() || (den != 0 && gcd(absVal(num), den)==1) )
           && ( !mpqPartValid()  || mpz_sgn(mpq_denref(mpq))!=0 );
}

inline FastRational::FastRational(word n, uword d) : state{State::WORD_VALID} {
    assert(d > 0);
    if (n == 0) {
        num = 0;
        den = 1;
    } else if (n > 0) {
        word common = gcd(uword(n), d);
        num = n/common;
        den = d/common;
    } else {
        word common = gcd(uword(-n), d);
        num = n/common;
        den = d/common;
    }
}

inline void addition(FastRational& dst, const FastRational& a, const FastRational& b) {
    if (a.wordPartValid() && b.wordPartValid()) {
        if (b.num == 0) {
            dst.num = a.num;
            dst.den = a.den;
        } else if (a.num == 0) {
            dst.num = b.num;
            dst.den = b.den;
        } else if (b.den == 1) {
            CHECK_WORD(dst.num, lword(a.num) + lword(b.num)*a.den);
            dst.den = a.den;
        } else if (a.den == 1) {
            CHECK_WORD(dst.num, lword(b.num) + lword(a.num)*b.den);
            dst.den = b.den;
        } else {
            lword c1 = lword(a.num)*b.den; // No overflow
            lword c2 = lword(b.num)*a.den; // No overflow
            lword n;
            CHECK_SUM_OVERFLOWS_LWORD(n, c1, c2); // Overflow possible
//            lword n = lword(a.num)*b.den + lword(b.num)*a.den;
            ulword d = ulword(a.den) * b.den;
            lword common = gcd(absVal(n), d);
            word zn;
            uword zd;
            if (common > 1) {
                CHECK_WORD(zn, n/common);
                CHECK_UWORD(zd, d/common);
            } else {
                CHECK_WORD(zn, n);
                CHECK_UWORD(zd, d);
            }
            dst.num = zn;
            dst.den = zd;
        }
        dst.kill_mpq();
        return;
    }
    overflow:
    a.force_ensure_mpq_valid();
    b.force_ensure_mpq_valid();
    dst.ensure_mpq_memory_allocated();
    mpq_add(dst.mpq, a.mpq, b.mpq);
    dst.state = State::MPQ_ALLOCATED_AND_VALID;
    dst.try_fit_word();
}

inline void substraction(FastRational& dst, const FastRational& a, const FastRational& b) {
    if (a.wordPartValid() && b.wordPartValid()) {
        if (b.num == 0) {
            dst.num = a.num;
            dst.den = a.den;
        }
        else if (a.num == 0) {
            if (b.num == WORD_MIN)
                goto overflow;
            dst.num = -b.num; // This overflows if b = -2147483648
            dst.den = b.den;
        }
        else if (b.den == 1) {
            CHECK_WORD(dst.num, lword(a.num) - lword(b.num)*a.den);
            dst.den = a.den;
        }
        else if (a.den == 1) {
            CHECK_WORD(dst.num, -lword(b.num) + lword(a.num)*b.den);
            dst.den = b.den;
        }
        else {
            lword n = lword(a.num)*b.den - lword(b.num)*a.den;
            ulword d = ulword(a.den) * b.den;
            lword common = gcd(absVal(n), d);
            word zn;
            uword zd;
            if (common > 1) {
                CHECK_WORD(zn, n/common);
                CHECK_UWORD(zd, d/common);
            } else {
                CHECK_WORD(zn, n);
                CHECK_UWORD(zd, d);
            }
            dst.num = zn;
            dst.den = zd;
        }
        dst.kill_mpq();
        return;
    }
    overflow:
    a.force_ensure_mpq_valid();
    b.force_ensure_mpq_valid();
    dst.ensure_mpq_memory_allocated();
    mpq_sub(dst.mpq, a.mpq, b.mpq);
    dst.state = State::MPQ_ALLOCATED_AND_VALID;
    dst.try_fit_word();
}

inline void multiplication(FastRational& dst, const FastRational& a, const FastRational& b) {
    if ((a.wordPartValid() && a.num==0) || (b.wordPartValid() && b.num==0)) {
        dst.num=0;
        dst.den=1;
        dst.setWordPartValid();
        dst.kill_mpq();
        return;
    }
    if (a.wordPartValid() && a.num==1 && a.den==1) {
        dst = b;
        return;
    }
    if (b.wordPartValid() && b.num==1 && b.den==1) {
        dst = a;
        return;
    }
    if (a.wordPartValid() && b.wordPartValid()) {
        word zn;
        uword zd;
        word common1 = gcd(absVal(a.num), b.den), common2 = gcd(a.den, absVal(b.num));
        lword k1, k2;
        ulword k3, k4; // Changed lword => ulword
        if (common1 > 1) {
            k1 = lword(a.num)/common1;
            k4 = ulword(b.den)/common1;
        } else {
            k1 = lword(a.num);
            k4 = ulword(b.den);
        }
        if (common2 > 1) {
            k2 = lword(b.num)/common2;
            k3 = ulword(a.den)/common2;
        } else {
            k2 = lword(b.num);
            k3 = ulword(a.den);
        }
        CHECK_WORD(zn, k1 * k2);
        CHECK_UWORD(zd, k3 * k4);
        dst.num = zn;
        dst.den = zd;
        dst.setWordPartValid();
        dst.kill_mpq();
        return;
    }
    overflow:
    a.force_ensure_mpq_valid();
    b.force_ensure_mpq_valid();
    dst.ensure_mpq_memory_allocated();
    mpq_mul(dst.mpq, a.mpq, b.mpq);
    dst.state = State::MPQ_ALLOCATED_AND_VALID;
    dst.try_fit_word();
}

inline void division(FastRational& dst, const FastRational& a, const FastRational& b) {
    if (a.wordPartValid() && b.wordPartValid()) {
        uword common1 = gcd(absVal(a.num), absVal(b.num));
        uword common2 = gcd(a.den, b.den);
        word zn;
        uword zd;
        CHECK_WORD(zn, (lword(a.num)/common1) * (b.den/common2));
        CHECK_UWORD(zd, ulword(absVal(b.num)/common1) * (a.den/common2));
        dst.num = zn;
        dst.den = zd;
        if ((b.num < 0 && a.num >= 0) || (b.num > 0 && a.num <= 0)) dst.num = -absVal(dst.num);
        if ((b.num > 0 && a.num >= 0) || (b.num < 0 && a.num <= 0)) dst.num = absVal(dst.num);
        dst.setWordPartValid();
        dst.kill_mpq();
        return;
    }
    overflow:
    a.force_ensure_mpq_valid();
    b.force_ensure_mpq_valid();
    dst.ensure_mpq_memory_allocated();
    mpq_div(dst.mpq, a.mpq, b.mpq);
    dst.state = State::MPQ_ALLOCATED_AND_VALID;
    dst.try_fit_word();
}

inline double FastRational::get_d() const {
    if (wordPartValid()) {
        return double(num)/double(den);
    } else {
        assert(mpqPartValid());
        return mpq_get_d(mpq);
    }
}

inline void additionAssign(FastRational& a, const FastRational& b) {
    if (b.wordPartValid()) {
        if (b.num == 0) return;
        if (a.wordPartValid()) {
            if (b.den == 1) {
                CHECK_WORD(a.num, lword(a.num) + lword(b.num)*a.den);
            } else if (a.num == 0) {
                a.num = b.num;
                a.den = b.den;
            } else {
                lword c1 = lword(a.num)*b.den; // No overflow
                lword c2 = lword(b.num)*a.den; // No overflow
                lword n;
                CHECK_SUM_OVERFLOWS_LWORD(n, c1, c2); // Overflow possible
//                lword n = lword(a.num)*b.den + lword(b.num)*a.den;
                ulword d = ulword(a.den) * b.den;
                lword common = gcd(absVal(n), d);
                word zn;
                uword zd;
                if (common > 1) {
                    CHECK_WORD(zn, n/common);
                    CHECK_UWORD(zd, d/common);
                } else {
                    CHECK_WORD(zn, n);
                    CHECK_UWORD(zd, d);
                }
                a.num = zn;
                a.den = zd;
            }
            a.kill_mpq();
            return;
        }
    }
    overflow:
    a.ensure_mpq_valid();
    b.force_ensure_mpq_valid();
    mpq_add(a.mpq, a.mpq, b.mpq);
    a.state = State::MPQ_ALLOCATED_AND_VALID;
    a.try_fit_word();
}

inline void substractionAssign(FastRational& a, const FastRational& b) {
    if (a.wordPartValid() && b.wordPartValid()) {
        uword common = gcd(a.den, b.den);
        COMPUTE_WORD(n1, lword(a.num) * (b.den / common));
        COMPUTE_WORD(n2, lword(b.num) * (a.den / common));
        lword n = lword(n1) - lword(n2);
        ulword d = ulword(a.den) * (b.den / common);
        common = gcd(absVal(n), d);
        word zn;
        uword zd;
        CHECK_WORD(zn, n/common);
        CHECK_UWORD(zd, d/common);
        a.num = zn;
        a.den = zd;
        a.kill_mpq();
        return;
    }
    overflow:
    a.ensure_mpq_valid();
    b.force_ensure_mpq_valid();
    mpq_sub(a.mpq, a.mpq, b.mpq);
    a.state = State::MPQ_ALLOCATED_AND_VALID;
    a.try_fit_word();
}

inline void multiplicationAssign(FastRational& a, const FastRational& b) {
    if (a.wordPartValid() && b.wordPartValid()) {
        lword common1 = gcd(absVal(a.num), b.den);
        lword common2 = gcd(a.den, absVal(b.num));
        word zn;
        uword zd;
        CHECK_WORD(zn, lword(a.num/common1) * (b.num/common2));
        CHECK_UWORD(zd, ulword(a.den/common2) * (b.den/common1));
        a.num = zn;
        a.den = zd;
        a.kill_mpq();
        return;
    }
    overflow:
    a.ensure_mpq_valid();
    b.force_ensure_mpq_valid();
    mpq_mul(a.mpq, a.mpq, b.mpq);
    a.state = State::MPQ_ALLOCATED_AND_VALID;
    a.try_fit_word();
}

inline void divisionAssign(FastRational& a, const FastRational& b) {
    if (a.wordPartValid() && b.wordPartValid()) {
        lword common1 = gcd(absVal(a.num), absVal(b.num));
        lword common2 = gcd(a.den, b.den);
        assert( common1 != 0 );
        assert( common2 != 0 );
        word zn;
        uword zd;
        if (b.num < 0) {
            CHECK_WORD(zn, -lword(a.num/common1) * (b.den/common2));
        } else {
            CHECK_WORD(zn,  lword(a.num/common1) * (b.den/common2));
        }
        CHECK_UWORD(zd, ulword(absVal(b.num)/common1) * (a.den/common2));
        a.den = zd;
        a.num = zn;
        a.kill_mpq();
        return;
    }
    overflow:
    a.ensure_mpq_valid();
    b.force_ensure_mpq_valid();
    mpq_div(a.mpq, a.mpq, b.mpq);
    a.state = State::MPQ_ALLOCATED_AND_VALID;
    a.try_fit_word();
}

inline unsigned FastRational::size() const {
    if (wordPartValid()) return 64;
    return mpz_sizeinbase(mpq_numref(mpq), 2) + mpz_sizeinbase(mpq_denref(mpq), 2);
}

inline FastRational FastRational::inverse() const {
    FastRational dest;
    if (wordPartValid()) {
        assert(num != 0);
        word zn;
        uword zd;
        if (num > 0) {
            CHECK_WORD(zn, den);
            CHECK_UWORD(zd, num);
        } else {
            CHECK_WORD(zn, -lword(den));
            CHECK_UWORD(zd, -lword(num));
        }
        dest.num = zn;
        dest.den = zd;
        return dest;
    }
    overflow:
    force_ensure_mpq_valid();
    dest.ensure_mpq_memory_allocated();
    mpq_inv(dest.mpq, mpq);
    dest.state = State::MPQ_ALLOCATED_AND_VALID;
    return dest;
}

inline FastRational abs(const FastRational& x) {
    if (x.sign() >= 0) {
        return x;
    } else {
        return -x;
    }
}

inline FastRational FastRational_inverse(const FastRational& x) {
    return x.inverse();
}

FastRational get_multiplicand(const vec<FastRational>& reals);
#endif
