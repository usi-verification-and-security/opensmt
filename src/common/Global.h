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

#define opensmt_error_() 		  { std::cerr << "# Error (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << std::endl; assert(false); ::exit( 1 ); }
#define opensmt_error( S )        { std::cerr << "; Error: " << S << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << std::endl; ::exit( 1 ); }
#define opensmt_error2( S, T )    { std::cerr << "; Error: " << S << " " << T << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << std::endl; ::exit( 1 ); }
#define opensmt_warning( S )      { std::cerr << "; Warning: " << S << std::endl; }
#define opensmt_warning2( S, T )  { cerr << "; Warning: " << S << " " << T << endl; }

#define reportf(format, args...) ( fflush(stdout), fprintf(stderr, format, ## args), fflush(stderr) )

#if ( __WORDSIZE == 64 )
#define BUILD_64
#endif

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


} // namespace opensmt


using opensmt::cpuTime;
using opensmt::memUsed;

#ifndef INT32_MAX
#define INT32_MAX 0x7fffffffL
#endif

#endif
