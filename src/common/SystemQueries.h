/*
 *  Copyright (c) 2008-2012, Roberto Bruttomesso <roberto.bruttomesso@gmail.com>
 *  Copyright (c) 2012-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef SYSTEMQUERIES_H
#define SYSTEMQUERIES_H


#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

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

#endif // SYSTEMQUERIES_H
