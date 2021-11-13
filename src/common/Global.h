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


#include "Map.h"

#define opensmt_error_() 		  { cerr << "# Error (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << endl; assert(false); ::exit( 1 ); }
#define opensmt_error( S )        { cerr << "; Error: " << S << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << endl; ::exit( 1 ); }
#define opensmt_error2( S, T )    { cerr << "; Error: " << S << " " << T << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << endl; ::exit( 1 ); }
#define opensmt_warning( S )      { cerr << "; Warning: " << S << endl; }
#define opensmt_warning2( S, T )  { cerr << "; Warning: " << S << " " << T << endl; }

#define reportf(format, args...) ( fflush(stdout), fprintf(stderr, format, ## args), fflush(stderr) )

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

using std::cout;
using std::cerr;
using std::endl;
using std::ostream;
using std::stringstream;
using std::ofstream;
using std::ifstream;

namespace opensmt {


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
    for (; field >= 0; field--) {
        int res = fscanf(in, "%d", &value);
        (void)res;
    }
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

    // For interpolation. When only 2 partitions
// are considered, these shorthands simplify
// readability
typedef enum
{
   I_UNDEF = 0
 , I_A     = 1
 , I_B     = 2
 , I_AB    = I_A | I_B
 , I_S     = 4
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
inline void andbit( ipartitions_t & ipres, const ipartitions_t & ip1, const ipartitions_t & ip2)
{ mpz_and( ipres.get_mpz_t( ), ip1.get_mpz_t( ), ip2.get_mpz_t( ) ); }
// Function: void mpz_or (mpz_t rop, mpz_t op1, mpz_t op2)
// Set rop to op1 bitwise inclusive-or op2.
inline void orbit( ipartitions_t & ipres, const ipartitions_t & ip1, const ipartitions_t & ip2)
{ mpz_ior( ipres.get_mpz_t( ), ip1.get_mpz_t( ), ip2.get_mpz_t( ) ); }
// Or-bit
// And-bit
// Basic operations
inline bool isAlocal ( const ipartitions_t & p, const ipartitions_t & mask ) { return (p & mask) != 0; }
inline bool isBlocal ( const ipartitions_t & p, const ipartitions_t & mask ) { return (p & ~mask) != 0; }
inline bool isAstrict( const ipartitions_t & p, const ipartitions_t & mask ) { return isAlocal( p, mask ) && !isBlocal( p, mask ); }
inline bool isBstrict( const ipartitions_t & p, const ipartitions_t & mask ) { return isBlocal( p, mask ) && !isAlocal( p, mask ); }
inline bool isAB     ( const ipartitions_t & p, const ipartitions_t & mask ) { return isAlocal( p, mask ) &&  isBlocal( p, mask ); }

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
} // namespace opensmt

static inline int getLog2Ceil(int i)
{
    if (i == 0 || i == 1) return 0;
    int r = 0;
    int j = i;
    while (i >>= 1) r++;

    if ((1 << r) ^ j) r++;
    return r;
}

using opensmt::cpuTime;
using opensmt::memUsed;
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

#ifndef INT32_MAX
#define INT32_MAX 0x7fffffffL
#endif

#endif
