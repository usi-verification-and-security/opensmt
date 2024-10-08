/*
Fast rationals
David Monniaux, VERIMAG 2008-2009

Copyright (c) 2008, 2009 Centre national de la recherche scientifique (CNRS)
 */
#ifndef FAST_RATIONALS_H
#define FAST_RATIONALS_H

#include <gmpxx.h>
#include <cassert>
#include <climits>
#include <cstdint>
#include <optional>
#include <stack>
#include <string>
#include <vector>

namespace opensmt {

typedef int32_t  word;
typedef uint32_t uword;
typedef int64_t  lword;
typedef uint64_t ulword;
#define WORD_MIN  INT_MIN
#define WORD_MAX  INT_MAX
#define UWORD_MAX UINT_MAX
#define LWORD_MIN LONG_MIN
#define LWORD_MAX LONG_MAX

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
    class mpqPool
    {
        std::stack<mpq_class> store; // uses deque as storage to avoid realloc
        std::stack<mpq_ptr, std::vector<mpq_ptr>> pool;
    public:
        mpq_ptr alloc();
        void release(mpq_ptr);
    };
    mutable State state;
    word num{0};
    uword den{1};
    mutable mpq_ptr mpq{nullptr};

    inline static mpqPool pool;
    inline static thread_local mpz_class temp;
    inline static mpz_ptr mpz() { return temp.get_mpz_t(); }


    // Bit masks for questioning state:
    static const unsigned char wordValidMask = 0x1;
    static const unsigned char mpqMemoryAllocatedMask = 0x2;
    static const unsigned char mpqValidMask = 0x4;

    // Methods for adjusting the inner state
    inline void setMpqMemoryAllocated() const {this->state |= State::MPQ_MEMORY_ALLOCATED; }
    inline void setMpqAllocatedAndValid() const {this->state |= State::MPQ_ALLOCATED_AND_VALID; }
    inline void setWordPartValid() const {this->state |= State::WORD_VALID; }
    inline void setWordPartInvalid() const { assert(mpqPartValid()); this->state = State::MPQ_ALLOCATED_AND_VALID; }
    inline void setOnlyWordPartValid() const {
        setWordPartValid();
        setMpqPartInvalid();
    }

    inline void setMpqPartInvalid() const {
        assert(wordPartValid());
        // clear the bit representing MPQ_VALID
        this->state = static_cast<State>(static_cast<state_t>(this->state) & ~(mpqValidMask));
        assert(not mpqPartValid() and wordPartValid());
    }
public:
    // Methods for questioning inner state
    inline bool wordPartValid() const { return  static_cast<state_t>(state) & wordValidMask; }
    inline bool wordAndMpqEqual() const;
    inline bool mpqMemoryAllocated() const { return  static_cast<state_t>(state) & mpqMemoryAllocatedMask; }
    inline bool mpqPartValid() const { return  static_cast<state_t>(state) & mpqValidMask; }

    //
    // Constructors
    //
    FastRational       () : state{State::WORD_VALID}, num(0), den(1) {}
    FastRational       (word x) : state{State::WORD_VALID}, num(x), den(1) {}
    FastRational       (uint32_t);
    inline FastRational(word n, uword d);
    // The string must be in the format accepted by mpq_set_str, e.g., "1/2"
    explicit FastRational(const char* s, const int base = 10);
    inline FastRational  (const FastRational &);
    inline FastRational  (FastRational&& other) noexcept;

    FastRational(mpz_t x);

    //
    // Destroyer
    //
    ~FastRational( ) { kill_mpq(); }
    FastRational & operator=(FastRational && other) {
        std::swap(this->state, other.state);
        std::swap(this->num, other.num);
        std::swap(this->den, other.den);
        std::swap(this->mpq, other.mpq);
        return *this;
    }

    void reset();
    inline FastRational & operator=( const FastRational & );
private:
    void kill_mpq()
    {
        if (mpqMemoryAllocated()) {
            pool.release(mpq);
            state = State::WORD_VALID;
        }
    }
    void ensure_mpq_valid() const {
        if (!mpqPartValid()) {
            assert(wordPartValid());
            if (!mpqMemoryAllocated()) {
                mpq = pool.alloc();
            }
            mpz_set_si(mpq_numref(mpq), num);
            mpz_set_ui(mpq_denref(mpq), den);
            setMpqAllocatedAndValid();
        }
    }

    void ensure_mpq_memory_allocated() const
    {
        if (!mpqMemoryAllocated()) {
            mpq = pool.alloc();
            setMpqMemoryAllocated();
        }
    }

    bool fitsWord() const
    {
        assert(not wordPartValid() and mpqPartValid()); // Do not call this method if word part is already valid
        return mpz_fits_sint_p(mpq_numref(mpq)) and mpz_fits_uint_p(mpq_denref(mpq));
    }

    //
    // Tries to convert the current rational
    // stored in mpq into word/uword
    //
    void try_fit_word()
    {
        assert(not wordPartValid() and mpqPartValid()); // Do not call this method if word part is already valid
        if (fitsWord()) {
            num = mpz_get_si(mpq_numref(mpq));
            den = mpz_get_ui(mpq_denref(mpq));
            setWordPartValid();
        }
    }
    friend inline void addition            (FastRational &, const FastRational &, const FastRational &);
    friend inline void subtraction         (FastRational &, const FastRational &, const FastRational &);
    friend inline void multiplication      (FastRational &, const FastRational &, const FastRational &);
    friend inline void division            (FastRational &, const FastRational &, const FastRational &);
    friend inline void additionAssign      (FastRational &, const FastRational &);
    friend inline void subtractionAssign   (FastRational &, const FastRational &);
    friend inline void multiplicationAssign(FastRational &, const FastRational &);
    friend inline void divisionAssign      (FastRational &, const FastRational &);
    friend FastRational gcd                (FastRational const &, FastRational const &);
    friend FastRational lcm                (FastRational const &, FastRational const &);
    friend FastRational fastrat_fdiv_q     (FastRational const & n, FastRational const & d);
    friend FastRational divexact           (FastRational const & n, FastRational const & d);

    static inline int compare(lword a, lword b) {
        if (a < b) return -1;
        else if (a > b) return 1;
        else return 0;
    }

    void print_(std::ostream& out) const;


public:
    void print           (std::ostream &) const;
    std::string   get_str() const;

    inline double get_d  () const;

    inline bool operator==(const FastRational& b) const;
    inline FastRational operator-() const;

    inline void negate();

    FastRational get_den() const {
        if (wordPartValid() && den <= INT32_MAX) {
            return FastRational((uword)den);
        }
        else {
            ensure_mpq_valid();
            return FastRational(mpq_denref(mpq));
        }
    }
    FastRational get_num() const {
        if (wordPartValid()) {
            return FastRational(num);
        }
        else {
            return FastRational(mpq_numref(mpq));
        }
    }

    std::optional<std::pair<word, uword>> tryGetNumDen() const {
        if (!wordPartValid()) return {};
        return std::make_pair(num, den);
    }

    mpq_class getMpq() const {
        if (wordPartValid()) {
            static_assert(sizeof(long) == 8);
            return mpq_class{static_cast<long>(num), static_cast<long>(den)};
        }
        assert(mpqPartValid());
        return mpq_class{mpq};
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
    inline FastRational ceil() const
    {
        if (isInteger())
            return *this;

        if (wordPartValid()) {
            word ret = absVal(num) / den; // Use correct abs
            if ( num < 0 ) ret = -ret; // Guaranteed not to overflow since den >= 2
            else ++ret;
            return ret;
        } else {
            mpz_cdiv_q(mpz(), mpq_numref(mpq), mpq_denref(mpq));
            return FastRational(mpz());
        }
    }
    inline FastRational floor() const
    {
        if (isInteger()) return *this;
        return ceil() - 1;
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
        subtraction(dest, *this, b);
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
        subtractionAssign(*this, b);
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
        assert(wordPartValid() or not fitsWord());
        return wordPartValid() and num == 0;
    }

    bool isOne() const {
        assert(wordPartValid() or not fitsWord());
        return wordPartValid() && num == 1 && den == 1;
    }


    // Return *this % d.  The return value will have the sign of d
    FastRational operator%(const FastRational& d) {
        assert(isInteger() && d.isInteger());
        if (wordPartValid() && d.wordPartValid()) {
            uword w = absVal(num % d.num);  // Largest value is absVal(INT_MAX % INT_MIN) = INT_MAX
            return (word)(d.num > 0 ? w : -w); // No overflow since 0 <= w <= INT_MAX
        }
        FastRational r = (*this) / d;
        r = r.floor();
        r = (*this) - r*d;
        return r;
    }
};

FastRational fastrat_fdiv_q(FastRational const & n, FastRational const & d);
FastRational fastrat_round_to_int(const FastRational& n);

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
        mpq = pool.alloc();
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
        setOnlyWordPartValid(); // MB: keeps mpq memory allocated if it already is
    }
    else {
        assert(x.mpqPartValid());
        if (!this->mpqMemoryAllocated()) {
            mpq = pool.alloc();
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
    ensure_mpq_valid();
    b.ensure_mpq_valid();
    return mpq_equal(mpq, b.mpq);
}

inline FastRational FastRational::operator-() const {
    if (this->wordPartValid() && num > WORD_MIN) {
        return FastRational(-num, den);
    } else {
        ensure_mpq_valid();
        FastRational x;
        x.mpq = pool.alloc();
        mpq_neg(x.mpq, mpq);
        x.state = State::MPQ_ALLOCATED_AND_VALID;
        x.try_fit_word(); // MB: If current value is 2^31, it does not fit word representation, but it's negation -2^31 does.
        return x;
    }
}

inline void FastRational::negate() {
    if (this->wordPartValid() && num > WORD_MIN) {
        num = -num;
        setMpqPartInvalid();
    } else {
        ensure_mpq_valid();
        mpq_neg(mpq, mpq);
        // MB: for the special case num == WORD_MIN && wordPartValid
        setWordPartInvalid();
        try_fit_word();
    }
    assert(isWellFormed());
}

inline int FastRational::compare(const FastRational& b) const {
    if (this->wordPartValid() && b.wordPartValid()) {
        if (b.den == den) {
            return compare(num, b.num);
        } else {
            return compare(lword(num)*b.den, lword(b.num)*den);
        }
    }
    ensure_mpq_valid();
    b.ensure_mpq_valid();
    return mpq_cmp(mpq, b.mpq);
}

inline int FastRational::sign() const {
    if (wordPartValid()) {
        // Based on benchmarking, the tricks in
        // https://stackoverflow.com/questions/14579920/fast-sign-of-integer-in-c
        // either degrade performance or have no effect apart from making code less readable
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
#define CHECK_WORD(var, value)                  \
    do {                                        \
        lword tmp = value;                      \
        if (tmp < WORD_MIN || tmp > WORD_MAX) { \
            goto overflow;                      \
        }                                       \
        var = tmp;                              \
    } while(0)                                  \

// Adapted from https://codereview.stackexchange.com/questions/37177/simple-method-to-detect-int-overflow
#define CHECK_SUM_OVERFLOWS_LWORD(var, s1, s2) \
    do {                                       \
        if (s1 > 0 and s2 > LWORD_MAX - s1) {  \
            goto overflow;                     \
        } if (s1 < 0 and s2 < LWORD_MIN - s1) {\
            goto overflow;                     \
        }                                      \
        var = s1 + s2;                         \
    } while (0)                                \

#define CHECK_SUB_OVERFLOWS_LWORD(var, s1, s2) \
    do {                                       \
        if (s1 >= 0 and s2 < s1 - LWORD_MAX) { \
            goto overflow;                     \
        } if (s1 < 0 and s2 > (s1 + 1) + LWORD_MAX) { \
            goto overflow;                     \
        }                                      \
        var = s1 - s2;                         \
    } while (0)                                \

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
    assert(wordPartValid() or not fitsWord());
    return (  wordPartValid() || mpqPartValid() )
           && ( !wordPartValid() || (den != 0 && gcd(absVal(num), den)==1) )
           && ( !mpqPartValid()  || mpz_sgn(mpq_denref(mpq))!=0 )
           && ( !(wordPartValid() && mpqPartValid()) || wordAndMpqEqual());
    // Check that if both wordPartValid() and mpqPartValid(), the are the same number
}

inline bool FastRational::wordAndMpqEqual() const {
    assert(wordPartValid() && mpqPartValid());
    uword int_den = mpz_get_ui(mpq_denref(mpq));
    word int_num = mpz_get_si(mpq_numref(mpq));
    return int_den == den and int_num == num;
}

inline FastRational::FastRational(word n, uword d) : state{State::WORD_VALID} {
    assert(d > 0);
    uword absN = absVal(n);
    uword common = gcd<uword>(absN, d);
    if (common > 1) {
        uword absNum = absN / common;
        assert(absNum <= WORD_MAX);
        num = n >= 0 ? static_cast<word>(absNum) : -static_cast<word>(absNum);
        den = d / common;
    } else {
        num = n;
        den = d;
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
        } else if (a.den == b.den and b.num > WORD_MIN and a.num == -b.num) {
            dst.num = 0;
            dst.den = 1;
        } else if (b.den == 1) {
            // Maximum sum here is INT_MAX + INT_MAX*UINT_MAX, which does not overflow.
            // Minimum sum here is INT_MIN + UINT_MAX*INT_MIN = 2^63, which does not overflow.
            // (a.num + b.num*a.den)/a.den is already canonicalized as can be seen with simple number theory.
            lword num_tmp = lword(a.num) + lword(b.num)*a.den;
            CHECK_WORD(dst.num, num_tmp);
            dst.den = a.den; // No overflow
        } else if (a.den == 1) {
            // See comments above.
            lword num_tmp = lword(b.num) + lword(a.num)*b.den;
            CHECK_WORD(dst.num, num_tmp);
            dst.den = b.den;
        } else {
            uword common = gcd(a.den, b.den);
            lword n1, n2;
            if (common != 1) {
                n1 = lword(a.num) * (b.den / common);
                n2 = lword(b.num) * (a.den / common);
            } else {
                n1 = lword(a.num) * b.den;
                n2 = lword(b.num) * a.den;
            }
            lword n;
            CHECK_SUM_OVERFLOWS_LWORD(n, n1, n2);
            ulword d = ulword(a.den) * (b.den / common);
            common = gcd(absVal(n), d);
            word zn;
            uword zd;
            if (common != 1) {
                CHECK_WORD(zn, n / common);
                CHECK_UWORD(zd, d / common);
            } else {
                CHECK_WORD(zn, n);
                CHECK_UWORD(zd, d);
            }
            dst.num = zn;
            dst.den = zd;
        }
        dst.setOnlyWordPartValid();
        assert(dst.isWellFormed());
        return;
    }
    overflow:
    a.ensure_mpq_valid();
    b.ensure_mpq_valid();
    dst.ensure_mpq_memory_allocated();
    mpq_add(dst.mpq, a.mpq, b.mpq);
    dst.state = State::MPQ_ALLOCATED_AND_VALID;
    dst.try_fit_word();
}

inline void subtraction(FastRational& dst, const FastRational& a, const FastRational& b) {
    if (a.wordPartValid() && b.wordPartValid()) {
        if (b.num == 0) {
            dst.num = a.num;
            dst.den = a.den;
        } else if (a.num == 0) {
            CHECK_WORD(dst.num, -lword(b.num));
            dst.den = b.den;
        } else if (a.den == b.den and a.num == b.num) {
            dst.num = 0;
            dst.den = 1;
        } else if (b.den == 1) {
            // Maximum subtraction here is INT_MAX - (INT_MIN)*(UINT_MAX) = 2^63-1 which does not overflow lword
            // Minimum subtraction here is INT_MIN - (INT_MAX)*(UINT_MAX) = -9223372028264841217 which does not underflow lword
            // (a.num - b.num*a.den) / a.den is already canonicalized
            CHECK_WORD(dst.num, lword(a.num) - lword(b.num)*a.den);
            dst.den = a.den;
        } else if (a.den == 1) {
            // (a.num*b.den - b.den)/b.den is already canonicalized.
            CHECK_WORD(dst.num, lword(a.num)*b.den - lword(b.num));
            dst.den = b.den;
        } else {
            uword common = gcd(a.den, b.den);
            lword n1, n2, n;
            ulword d;
            if (common != 1) {
                // Worst case for n1-n2 seems to be
                // - 2147483647/4294967292 - 2147483645/4294967294
                // This does not overflow.  The positive case is the same
                n1 = lword(a.num) * (b.den / common);
                n2 = lword(b.num) * (a.den / common);
                n = n1 - n2;
//                CHECK_SUB_OVERFLOWS_LWORD(n, n1, n2);
                d = ulword(a.den) * (b.den / common);
            } else {
                n1 = lword(a.num) * b.den;
                n2 = lword(b.num) * a.den;
                // Consider -2147483645/4294967294 - 2147483647/4294967295.  The following underflows lword
                CHECK_SUB_OVERFLOWS_LWORD(n, n1, n2);
                d = ulword(a.den) * b.den;
            }

            common = gcd(absVal(n), d);
            word zn;
            uword zd;
            if (common != 1) {
                CHECK_WORD(zn, n / common);
                CHECK_UWORD(zd, d / common);
            } else {
                CHECK_WORD(zn, n);
                CHECK_UWORD(zd, d);
            }
            dst.num = zn;
            dst.den = zd;
        }
        dst.setOnlyWordPartValid();
        assert(dst.isWellFormed());
        return;
    }
    overflow:
    a.ensure_mpq_valid();
    b.ensure_mpq_valid();
    dst.ensure_mpq_memory_allocated();
    mpq_sub(dst.mpq, a.mpq, b.mpq);
    dst.state = State::MPQ_ALLOCATED_AND_VALID;
    dst.try_fit_word();
}

inline void multiplication(FastRational& dst, const FastRational& a, const FastRational& b) {
    if ((a.wordPartValid() && a.num==0) || (b.wordPartValid() && b.num==0)) {
        dst.num=0;
        dst.den=1;
        dst.setOnlyWordPartValid();
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
        uword common1 = gcd(absVal(a.num), b.den), common2 = gcd(a.den, absVal(b.num));
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
        dst.setOnlyWordPartValid();
        return;
    }
    overflow:
    a.ensure_mpq_valid();
    b.ensure_mpq_valid();
    dst.ensure_mpq_memory_allocated();
    mpq_mul(dst.mpq, a.mpq, b.mpq);
    dst.state = State::MPQ_ALLOCATED_AND_VALID;
    dst.try_fit_word();
}

inline void division(FastRational& dst, const FastRational& a, const FastRational& b) {
    if (b.wordPartValid() && b.num == 1 && b.den == 1) {
        dst = a;
        return;
    }
    if (a.wordPartValid() && a.num == 0) {
        dst = 0;
        return;
    }
    if (a.wordPartValid() && b.wordPartValid()) {
        if (a.num == b.num && a.den == b.den) {
            dst.num = 1;
            dst.den = 1;
            dst.setOnlyWordPartValid();
            return;
        }
        uword common1 = gcd(absVal(a.num), absVal(b.num));
        uword common2 = gcd(a.den, b.den);
        word zn;
        uword zd;
        CHECK_WORD(zn, ulword(absVal(a.num)/common1) * (b.den/common2));
        CHECK_UWORD(zd, ulword(absVal(b.num)/common1) * (a.den/common2));

        // Note: dst and a or b might be the same FastRational.
        bool b_num_lt_0 = b.num < 0;
        bool a_num_ge_0 = a.num >= 0;
        bool b_num_gt_0 = b.num > 0;
        bool a_num_le_0 = a.num <= 0;

        if ((b_num_lt_0 && a_num_ge_0) || (b_num_gt_0 && a_num_le_0)) { // Flip the sign if necessary
            zn = -zn; // Cannot overflow since zn is a positive word
        }

        dst.num = zn;
        dst.den = zd;
        dst.setOnlyWordPartValid();
        assert(dst.isWellFormed());
        return;
    }
    overflow:
    a.ensure_mpq_valid();
    b.ensure_mpq_valid();
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
            a.setOnlyWordPartValid();
            assert(a.isWellFormed());
            return;
        }
    }
    overflow:
    a.ensure_mpq_valid();
    b.ensure_mpq_valid();
    mpq_add(a.mpq, a.mpq, b.mpq);
    a.state = State::MPQ_ALLOCATED_AND_VALID;
    a.try_fit_word();
}

inline void subtractionAssign(FastRational& a, const FastRational& b) {
    if (a.wordPartValid() && b.wordPartValid()) {
        uword common = gcd(a.den, b.den);
        COMPUTE_WORD(n1, lword(a.num) * (b.den / common));
        COMPUTE_WORD(n2, lword(b.num) * (a.den / common));
        lword n = lword(n1) - lword(n2); // Cannot overflow
        ulword d = ulword(a.den) * (b.den / common);
        common = gcd(absVal(n), d);
        word zn;
        uword zd;
        if (common > 1) {
            CHECK_WORD(zn, n / common);
            CHECK_UWORD(zd, d / common);
        } else {
            CHECK_WORD(zn, n);
            CHECK_UWORD(zd, d);
        }
        a.num = zn;
        a.den = zd;
        a.setOnlyWordPartValid();
        assert(a.isWellFormed());
        return;
    }
    overflow:
    a.ensure_mpq_valid();
    b.ensure_mpq_valid();
    mpq_sub(a.mpq, a.mpq, b.mpq);
    a.state = State::MPQ_ALLOCATED_AND_VALID;
    a.try_fit_word();
}

inline void multiplicationAssign(FastRational& a, const FastRational& b) {
    if (a.wordPartValid() && b.wordPartValid()) {
        uword common1 = gcd(absVal(a.num), b.den);
        uword common2 = gcd(a.den, absVal(b.num));
        word zn;
        uword zd;
        // Without the absVal, this fails for a.num < 0 when common1 > 1 and b.num < 0 when common2 > 1 since the result of the division is unsigned.
        CHECK_WORD(zn, lword(common1 > 1 ? absVal(a.num)/common1 : absVal(a.num)) * (common2 > 1 ? absVal(b.num)/common2 : absVal(b.num)));
        CHECK_UWORD(zd, ulword(common2 > 1 ? a.den/common2 : a.den) * (common1 > 1 ? b.den/common1 : b.den));

        bool b_num_lt_0 = b.num < 0;
        bool a_num_ge_0 = a.num >= 0;
        bool b_num_gt_0 = b.num > 0;
        bool a_num_le_0 = a.num <= 0;

        if ((b_num_lt_0 && a_num_ge_0) || (b_num_gt_0 && a_num_le_0)) { // Flip sign
            zn = -zn; // Cannot overflow since zn is a positive word
        }

        a.num = zn;
        a.den = zd;
        a.setOnlyWordPartValid();
        assert(a.isWellFormed());
        return;
    }
    overflow:
    a.ensure_mpq_valid();
    b.ensure_mpq_valid();
    mpq_mul(a.mpq, a.mpq, b.mpq);
    a.state = State::MPQ_ALLOCATED_AND_VALID;
    a.try_fit_word();
}

inline void divisionAssign(FastRational& a, const FastRational& b) {
    if (a.wordPartValid() && b.wordPartValid()) {
        uword common1 = gcd(absVal(a.num), absVal(b.num));
        uword common2 = gcd(a.den, b.den);
        word zn;
        uword zd;
        CHECK_WORD(zn, ulword(absVal(a.num) / common1) * (b.den / common2));
        CHECK_UWORD(zd, ulword(absVal(b.num) / common1) * (a.den / common2));

        bool b_num_lt_0 = b.num < 0;
        bool a_num_ge_0 = a.num >= 0;
        bool b_num_gt_0 = b.num > 0;
        bool a_num_le_0 = a.num <= 0;

        if ((b_num_lt_0 && a_num_ge_0) || (b_num_gt_0 && a_num_le_0)) { // Flip sign
            zn = -zn; // Cannot overflow since zn is a positive word
        }

        a.den = zd;
        a.num = zn;
        a.setOnlyWordPartValid();
        assert(a.isWellFormed());
        return;
    }
    overflow:
    a.ensure_mpq_valid();
    b.ensure_mpq_valid();
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
    ensure_mpq_valid();
    dest.ensure_mpq_memory_allocated();
    mpq_inv(dest.mpq, mpq);
    dest.state = State::MPQ_ALLOCATED_AND_VALID;
    dest.try_fit_word();
    assert(dest.isWellFormed());
    return dest;
}

inline FastRational abs(FastRational const & x) {
    if (x.sign() >= 0) {
        return x;
    } else {
        return -x;
    }
}

FastRational get_multiplicand(const std::vector<FastRational>& reals);

}

#endif
