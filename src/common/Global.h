/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>
        Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2017, Antti Hyvarinen
                          2008 - 2012, Roberto Bruttomesso

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

#ifndef GLOBAL_H
#define GLOBAL_H

#define USE_GMP        1
#define FAST_RATIONALS 1

#include <cstring>
// Workaround to allow compiling with gcc 4.9.0 and versions of gmp up
// to 5.1.3 (see https://gcc.gnu.org/gcc-4.9/porting_to.html)
#include <cstddef>
#include <gmp.h>
#include <gmpxx.h>
#include <cassert>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <list>
#include <sstream>
#include <iostream>
#include <fstream>
#include <queue>
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
#include <stdint.h>
#include <limits.h>
#include <cstdlib>

#include "FastRational.h"
#include "Map.h"

#define opensmt_error_() 		  { cerr << "# Error (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << endl; assert(false); ::exit( 1 ); }
#define opensmt_error( S )        { cerr << "; Error: " << S << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << endl; ::exit( 1 ); }
#define opensmt_error2( S, T )    { cerr << "; Error: " << S << " " << T << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << endl; ::exit( 1 ); }
#define opensmt_warning( S )      { cerr << "; Warning: " << S << endl; }
#define opensmt_warning2( S, T )  { cerr << "; Warning: " << S << " " << T << endl; }

#if ( __WORDSIZE == 64 )
#define BUILD_64
#endif

using std::set;
using std::map;
using std::vector;
using std::string;
using std::pair;
using std::make_pair;
using std::list;

//#if defined( __GNUC__ ) && (__GNUC__ > 4 || (__GNUC__ == 4 && __GNUC_MINOR__ >= 3))
//using __gnu_pbds::priority_queue;
//using __gnu_pbds::pairing_heap_tag;
//#else
//#error "This version of OpenSMT2 requires at least gcc 4.3"
//using pb_ds::priority_queue;
//using pb_ds::pairing_heap_tag;
//#endif

using std::cout;
using std::cerr;
using std::endl;
using std::ostream;
using std::stringstream;
using std::ofstream;
using std::ifstream;

namespace opensmt {

#if FAST_RATIONALS
typedef FastRational Real;
typedef mpz_class Integer;
#else
typedef mpq_class Real;
#endif

void static inline wordToBinary(const opensmt::Integer x, char*& bin, const int width)
{
    bin = (char*) malloc(width+1);

    int p = 0;
    opensmt::Integer one = 1;
    for (opensmt::Integer i = (one << (width-1)); i > 0; i >>= 1)
        bin[p++] = ((x&i) == i) ? '1' : '0';
    bin[p] = '\0';
}

void static inline wordToBinary(const unsigned x, char*& bin, const int width)
{
    bin = (char*) malloc(width+1);

    int p = 0;
    opensmt::Integer one = 1;
    for (opensmt::Integer i = (one << (width-1)); i > 0; i >>= 1)
        bin[p++] = ((x&i) == i) ? '1' : '0';
    bin[p] = '\0';
}


bool static inline isDigit(char c)
{
    return (c >= '0' && c <= '9');
}
bool static inline isPosDig(char c)
{
    return (c > '0' && c <= '9');
}

void static inline normalize(char*& rat, const char* flo, bool is_neg)
{
    mpq_t num;
    mpq_init(num);
    int val = mpq_set_str(num, flo, 0);
    assert(val != -1);
    mpq_canonicalize(num);
    if (is_neg)
        mpq_neg(num, num);
    gmp_asprintf(&rat, "%Qd", num);
    mpq_clear(num);
}

static inline bool isPowOfTwo(int b)
{
    return b && !(b & (b-1));
}

static inline int getLogFromPowOfTwo(int l)
{
    assert(isPowOfTwo(l));
    if (l == 1) return 0;
    int n = 0;
    while ((2 << (n++)) != l);
    return n;
}

class strConvException : std::exception
{
    char* reason;
public:
    strConvException(const char* reason_) {
        asprintf(&reason, "Error converting string to rational.  %s is not a legal rational", reason_);
    }
    virtual const char* what() const noexcept
    {
        return reason;
    }
    ~strConvException() { free(reason); }
};

bool static inline stringToRational(char*& rat, const char* flo)
{
    int nom_l = 0;
    int den_l = 1;
    int state = 0;
    int zeroes = 0;
    bool is_frac = false;
    bool is_neg = false;

    if (flo[0] == '-') { flo++; is_neg = true; }

    for (int i = 0; flo[i] != '\0'; i++) {
        if (state == 0 && flo[i] == '0') {}
        else if (state == 0 && isPosDig(flo[i])) { nom_l ++; state = 1; }
        else if (state == 0 && flo[i] == '.')    { state = 4; }
        else if (state == 0 && flo[i] == '/')    { state = 5; is_frac = true; }
        else if (state == 1 && isDigit(flo[i]))  { nom_l ++; state = 1; }
        else if (state == 1 && flo[i] == '.')    { state = 2; }
        else if (state == 1 && flo[i] == '/')    { state = 5; is_frac = true; }
        else if (state == 2 && flo[i] == '0')    { zeroes ++; state = 3; }
        else if (state == 2 && isPosDig(flo[i])) { nom_l ++; state = 2; }
        else if (state == 3 && flo[i] == '0')    { zeroes ++; state = 3; }
        else if (state == 3 && isPosDig(flo[i])) { nom_l += zeroes + 1; zeroes = 0; state = 2; }
        else if (state == 4 && flo[i] == '0')    { state = 4; }
        else if (state == 4 && isPosDig(flo[i])) { nom_l ++; state = 2; }
        // We come here if it is a fraction already
        else if (state == 5 && isDigit(flo[i]))  { state = 5; }
        else { throw strConvException(flo); }
    }

    if (is_frac) {
        normalize(rat, flo, is_neg);
        return true;
    }

    if (nom_l == 0) {
        normalize(rat, "0", false);
        return true;
    }

    state = 0;
    zeroes = 0;
    for (int i = 0; flo[i] != '\0'; i++) {
        if (state == 0 && isDigit(flo[i])) { state = 0; }
        else if (state == 0 && flo[i] == '.')   { state = 1; }
        else if (state == 1 && isPosDig(flo[i])) { state = 1; den_l ++; }
        else if (state == 1 && flo[i] == '0')    { state = 2; zeroes ++; }
        else if (state == 2 && flo[i] == '0')    { state = 2; zeroes ++; }
        else if (state == 2 && isPosDig(flo[i])) { state = 1; den_l += zeroes + 1; zeroes = 0; }
    }

//    printf("The literal %s, once converted, will have denominator of length %d and nominator of length %d characters\n", flo, den_l, nom_l);
    char* rat_tmp = (char*)malloc(nom_l+den_l+2);
    rat_tmp[0] = '\0';

    int i, j;
    state = -1;
    for (i = j = 0; j < nom_l; i++) {
        assert(flo[i] != '\0');
        if (state == -1 && flo[i] != '.' && flo[i] != '0') { rat_tmp[j++] = flo[i]; state = 0; }
        else if (state == -1 && flo[i] == '.') {}
        else if (state == -1 && flo[i] == '0') {}
        else if (state == 0 && flo[i] != '.') { rat_tmp[j++] = flo[i]; }
        else if (state == 0 && flo[i] == '.') {}
    }
    rat_tmp[j++] = '/';
    rat_tmp[j++] = '1';
    for (i = 0; i < den_l-1; i++) rat_tmp[j++] = '0';
    rat_tmp[j] = '\0';
    normalize(rat, rat_tmp, is_neg);
    free(rat_tmp);
    return true;
}



#define Pair( T ) pair< T, T >

typedef int       enodeid_t;


typedef enodeid_t snodeid_t;
typedef enodeid_t sortid_t;
#ifdef BUILD_64
typedef long enodeid_pair_t;
inline enodeid_pair_t encode( enodeid_t car, enodeid_t cdr )
{
  enodeid_pair_t p = car;
  p = p<<(sizeof(enodeid_t)*8);
  enodeid_pair_t q = cdr;
  p |= q;
  return p;
}
#else
typedef Pair( enodeid_t ) enodeid_pair_t;
inline enodeid_pair_t encode( enodeid_t car, enodeid_t cdr )
{ return make_pair( car, cdr ); }
#endif
typedef enodeid_pair_t snodeid_pair_t;

#define STATISTICS

// Set the bit B to 1 and leaves the others to 0
#define SETBIT( B ) ( 1 << (B) )

struct Logic_t {
    int x;
    const char* str;
    bool operator== (const Logic_t& o) const { return x == o.x; }
    bool operator!= (const Logic_t& o) const { return x != o.x; }
};

static struct Logic_t UNDEF = {-1, "UNDEF"};
static struct Logic_t EMPTY = {0, "EMPTY"};
static struct Logic_t QF_UF = {1, "QF_UF"};
static struct Logic_t QF_CUF = {1, "QF_CUF"};
static struct Logic_t QF_BV = {2, "QF_BV"};
static struct Logic_t QF_RDL = {3, "QF_RDL"};
static struct Logic_t QF_IDL = {4, "QF_IDL"};
static struct Logic_t QF_LRA = {5, "QF_LRA"};
static struct Logic_t QF_LIA = {6, "QF_LIA"};
static struct Logic_t QF_UFRDL = {7, "QF_UFRDL"};
static struct Logic_t QF_UFIDL = {8, "QF_UFIDL"};
static struct Logic_t QF_UFLRA = {9, "QF_UFLRA"};
static struct Logic_t QF_UFLIA = {10, "QF_UFLIA"};
static struct Logic_t QF_UFBV = {11, "QF_UFBV"};
static struct Logic_t QF_AX = {12, "QF_AX"};
static struct Logic_t QF_AXDIFF = {13, "QF_AXDIFF"};
static struct Logic_t QF_BOOL = {14, "QF_BOOL"};
static struct Logic_t QF_AUFBV = {15, "QF_AUFBV"};
static struct Logic_t QF_CT = {16, "QF_CT"};


static inline double cpuTime(void)
{
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000;
}

#if defined(__linux__)
static inline int memReadStat(int field)
{
    char name[256];
    pid_t pid = getpid();
    sprintf(name, "/proc/%d/statm", pid);
    FILE*   in = fopen(name, "rb");
    if (in == NULL) return 0;
    int value;
    for (; field >= 0; field--)
        fscanf(in, "%d", &value);
    fclose(in);
    return value;
}

static inline uint64_t memUsed() { return (uint64_t)memReadStat(0) * (uint64_t)getpagesize(); }

#elif defined(__FreeBSD__) || defined(__OSX__) || defined(__APPLE__)
static inline uint64_t memUsed()
{
  char name[256];
  FILE *pipe;
  char buf[1024];
  uint64_t value=0;
  pid_t pid = getpid();
  sprintf(name,"ps -o rss -p %d | grep -v RSS", pid);
  pipe = popen(name, "r");
  if (pipe)
  {
    fgets(buf, 1024, pipe);
    value = 1024 * strtoul(buf, NULL, 10);
    pclose(pipe);
  }
  return value;
}
#else // stub to support every platform
static inline uint64_t memUsed() {return 0; }
#endif

#define CNF_STR "CNF_%d_%d"
#define ITE_STR "ITE_%d"
#define SPL_STR "SPL_%d"
#define UNC_STR "UNC_%d"
#define IND_STR "IND_%d_%d"
#define ELE_STR "ELE_%d"
#define ARR_STR "ARR_%d"

#ifdef PRODUCE_PROOF
// For interpolation. When only 2 partitions
// are considered, these shorthands simplify
// readability
typedef enum
{
   I_UNDEF = 0
 , I_A     = 1
 , I_B     = 2
 , I_AB    = I_A | I_B
} icolor_t;
// For interpolation. Type that has to
// be used to store multiple partitions for
// a term
typedef mpz_class ipartitions_t;
// Set-bit
inline void setbit( ipartitions_t & p, const unsigned b ) { mpz_setbit( p.get_mpz_t( ), b ); }
inline void clrbit( ipartitions_t & p, const unsigned b ) { mpz_clrbit( p.get_mpz_t( ), b ); }
inline int tstbit( const ipartitions_t & p, const unsigned b ) { return mpz_tstbit( p.get_mpz_t( ), b ); }
// Function: void mpz_and (mpz_t rop, mpz_t op1, mpz_t op2)
// Set rop to op1 bitwise-and op2.
inline void andbit( ipartitions_t & ipres, ipartitions_t & ip1, ipartitions_t & ip2)
{ mpz_and( ipres.get_mpz_t( ), ip1.get_mpz_t( ), ip2.get_mpz_t( ) ); }
// Function: void mpz_or (mpz_t rop, mpz_t op1, mpz_t op2)
// Set rop to op1 bitwise inclusive-or op2.
inline void orbit( ipartitions_t & ipres, ipartitions_t & ip1, const ipartitions_t & ip2)
{ mpz_ior( ipres.get_mpz_t( ), ip1.get_mpz_t( ), ip2.get_mpz_t( ) ); }
inline void orbit( ipartitions_t & ipres, ipartitions_t & ip1, ipartitions_t & ip2)
{ mpz_ior( ipres.get_mpz_t( ), ip1.get_mpz_t( ), ip2.get_mpz_t( ) ); }
// Or-bit
// And-bit
// Basic operations
inline bool isABmixed( const ipartitions_t & p ) { return p % 2 == 1; }
inline bool isAlocal ( const ipartitions_t & p, const ipartitions_t & mask ) { return !isABmixed( p ) && (p & mask) != 0; }
inline bool isBlocal ( const ipartitions_t & p, const ipartitions_t & mask ) { return !isABmixed( p ) && (p & ~mask) != 0; }
inline bool isAstrict( const ipartitions_t & p, const ipartitions_t & mask ) { return !isABmixed( p ) && isAlocal( p, mask ) && !isBlocal( p, mask ); }
inline bool isBstrict( const ipartitions_t & p, const ipartitions_t & mask ) { return !isABmixed( p ) && isBlocal( p, mask ) && !isAlocal( p, mask ); }
inline bool isAB     ( const ipartitions_t & p, const ipartitions_t & mask ) { return !isABmixed( p ) && isAlocal( p, mask ) &&  isBlocal( p, mask ); }
#endif

#ifdef PRODUCE_PROOF
// To specify the tree structure of a collection of partitions
// NOTE Partitions should be tagged with consecutive ids >=1
class InterpolationTree
{
public:
    InterpolationTree(int _partition_id):
        partition_id(_partition_id),
        parent(NULL)
{}

void addChild (InterpolationTree* _tree){
        children.insert(_tree);
        (*_tree).setParent(this);
    }

    void setParent(InterpolationTree* _parent){
        parent = _parent;
    }

    int getPartitionId() { return partition_id; }
    set<InterpolationTree*>& getChildren() { return children; }
    InterpolationTree* getParent() {return parent; }

private:
    // NOTE if the tree has N nodes, the partition ids go from 1 to N
    int partition_id;                         // The integer corresponding to the partition id
    set<InterpolationTree*>  children;        // The children of the node in the tree
    InterpolationTree* parent;
};
#endif
} // namespace opensmt

struct EnodeIdHash {
    opensmt::enodeid_t operator() (const opensmt::enodeid_t s) const {
        return s; }
};

template <>
struct Equal<const opensmt::enodeid_t> {
    bool operator() (const opensmt::enodeid_t s1, const opensmt::enodeid_t s2) const {
        return s1 == s2; }
};

static inline int getLog2Ceil(int i)
{
    if (i == 0 || i == 1) return 0;
    int r = 0;
    int j = i;
    while (i >>= 1) r++;

    if ((1 << r) ^ j) r++;
    return r;
}

using opensmt::enodeid_t;
using opensmt::snodeid_t;
using opensmt::sortid_t;
using opensmt::enodeid_pair_t;
using opensmt::encode;
using opensmt::Logic_t;
using opensmt::UNDEF;
using opensmt::EMPTY;        
using opensmt::QF_UF;        
using opensmt::QF_BV;        
using opensmt::QF_RDL;        
using opensmt::QF_IDL;       
using opensmt::QF_LRA;       
using opensmt::QF_LIA;       
using opensmt::QF_UFRDL;      
using opensmt::QF_UFIDL;
using opensmt::QF_UFLRA;     
using opensmt::QF_UFLIA;     
using opensmt::QF_UFBV;     
using opensmt::QF_AUFBV;      
using opensmt::QF_AX;  
using opensmt::QF_AXDIFF;  
using opensmt::QF_BOOL;       
using opensmt::QF_CT;       
using opensmt::cpuTime;       
using opensmt::memUsed;       
#ifdef PRODUCE_PROOF
using opensmt::icolor_t;
using opensmt::I_UNDEF;
using opensmt::I_A;
using opensmt::I_B;
using opensmt::I_AB;
using opensmt::ipartitions_t;
using opensmt::setbit;
using opensmt::clrbit;
using opensmt::ipartitions_t;
using opensmt::isAlocal; 
using opensmt::isBlocal;
using opensmt::isAstrict;
using opensmt::isBstrict;
using opensmt::isAB;
using opensmt::isABmixed;
#endif

#ifndef INT32_MAX
#define INT32_MAX 0x7fffffffL
#endif

#endif
