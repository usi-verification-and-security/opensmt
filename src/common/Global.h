/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#ifndef GLOBAL_H
#define GLOBAL_H

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
#include <ext/hash_map>
#include <ext/hash_set>
#include <ext/pb_ds/priority_queue.hpp>
#include <ext/pb_ds/tag_and_trait.hpp>
#include <ext/algorithm>
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
#include <stdint.h>
#include <limits.h>

#include "minisat/mtl/Map.h"

#define opensmt_error( S )        { cerr << "# Error: " << S << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << endl; exit( 1 ); }
#define opensmt_error2( S, T )    { cerr << "# Error: " << S << " " << T << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << endl; exit( 1 ); }
#define opensmt_warning( S )      { cerr << "# Warning: " << S << endl; }
#define opensmt_warning2( S, T )  { cerr << "# Warning: " << S << " " << T << endl; }

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

using __gnu_cxx::is_heap;
using __gnu_cxx::hash_map;
using __gnu_cxx::hash_set;
using __gnu_cxx::hash;

#if defined( __GNUC__ ) && (__GNUC__ > 4 || (__GNUC__ == 4 && __GNUC_MINOR__ >= 3))
using __gnu_pbds::priority_queue;
using __gnu_pbds::pairing_heap_tag;
#else
#error "This version of OpenSMT requires at least gcc 4.3"
using pb_ds::priority_queue;
using pb_ds::pairing_heap_tag;
#endif

using std::cout;
using std::cerr;
using std::endl;
using std::ostream;
using std::stringstream;
using std::ofstream;
using std::ifstream;

#define USE_GMP        1
#define FAST_RATIONALS 1

#if FAST_RATIONALS
#include "FastRationals.h"
#endif

namespace opensmt {

#if FAST_RATIONALS
typedef FastRational Real;
typedef FastInteger Integer;
#elif USE_GMP
typedef mpq_class Real;
typedef mpz_class Integer;
#else
typedef double Real;
typedef long Integer;
#endif


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

#ifndef SMTCOMP
#define STATISTICS
#endif

// Set the bit B to 1 and leaves the others to 0
#define SETBIT( B ) ( 1 << (B) )

typedef enum
{
    UNDEF         // Undefined logic
  , EMPTY         // Empty, for the template solver
  , QF_UF         // Uninterpreted Functions
  , QF_BV         // BitVectors
  , QF_RDL        // Real difference logics
  , QF_IDL        // Integer difference logics
  , QF_LRA        // Real linear arithmetic
  , QF_LIA        // Integer linear arithmetic
  , QF_UFRDL      // UF + RDL
  , QF_UFIDL      // UF + IDL
  , QF_UFLRA      // UF + LRA
  , QF_UFLIA      // UF + LIA
  , QF_UFBV       // UF + BV
  , QF_AUFBV      // Arrays + UF + BV
  , QF_AX	  // Arrays with extensionality
  , QF_AXDIFF	  // Arrays with extensionality and diff
  , QF_BOOL       // Purely SAT instances
  , QF_CT	  // Cost
// DO NOT REMOVE THIS COMMENT !!
// IT IS USED BY CREATE_THEORY.SH SCRIPT !!
// NEW_THEORY_INIT
} logic_t;

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
// Or-bit
// And-bit
// Basic operations
inline bool isABmixed( const ipartitions_t & p ) { return p % 2 == 1; }
inline bool isAlocal ( const ipartitions_t & p, const ipartitions_t & mask ) { return !isABmixed( p ) && (p & ~mask) != 0; }
inline bool isBlocal ( const ipartitions_t & p, const ipartitions_t & mask ) { return !isABmixed( p ) && (p &  mask) != 0; }
inline bool isAstrict( const ipartitions_t & p, const ipartitions_t & mask ) { return !isABmixed( p ) && isAlocal( p, mask ) && !isBlocal( p, mask ); }
inline bool isBstrict( const ipartitions_t & p, const ipartitions_t & mask ) { return !isABmixed( p ) && isBlocal( p, mask ) && !isAlocal( p, mask ); }
inline bool isAB     ( const ipartitions_t & p, const ipartitions_t & mask ) { return !isABmixed( p ) && isAlocal( p, mask ) &&  isBlocal( p, mask ); }
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

using opensmt::Real;
using opensmt::Integer;
using opensmt::enodeid_t;
using opensmt::snodeid_t;
using opensmt::sortid_t;
using opensmt::enodeid_pair_t;
using opensmt::encode;
using opensmt::logic_t;
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

#endif
