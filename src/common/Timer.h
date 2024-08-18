/*********************************************************************
 Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

 OpenSMT2 -- Copyright (C) 2012 - 2016, Antti Hyvarinen
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

#ifndef TIMER_H
#define TIMER_H

#include <cassert>
#include <cstring>
#include <iostream>
#include <sys/resource.h>
#include <sys/time.h>

namespace opensmt {
// A c++ wrapper for struct timeval
class BTime {
public:
    BTime() = default;
    BTime(const struct timeval & tv) : tv_sec(tv.tv_sec), tv_usec(tv.tv_usec) {}
    void operator-=(BTime const & subst) {
        tv_sec -= subst.tv_sec;
        tv_usec -= subst.tv_usec;
    }
    BTime operator-(BTime const & subst) {
        BTime out;
        out.tv_sec = tv_sec - subst.tv_sec;
        out.tv_usec = tv_usec - subst.tv_usec;
        return out;
    }
    BTime & operator+=(BTime const & other) {
        tv_sec += other.tv_sec;
        tv_usec += other.tv_usec;
        return *this;
    }
    double getTime() { return tv_sec + tv_usec / (double)1000000; }

private:
    time_t tv_sec{0};
    suseconds_t tv_usec{0};
};

class TimeVal {
public:
    TimeVal() = default;
    TimeVal(BTime const & usrtime, BTime const & systime) : usrtime(usrtime), systime(systime) {}
    TimeVal(const struct rusage & res_usage) : usrtime(res_usage.ru_utime), systime(res_usage.ru_stime) {}

    void operator-=(TimeVal const & subst) {
        usrtime -= subst.usrtime;
        systime -= subst.systime;
    }
    TimeVal operator-(TimeVal const & subst) {
        TimeVal out;
        out.usrtime = usrtime - subst.usrtime;
        out.systime = systime - subst.systime;
        return out;
    }
    TimeVal & operator+=(TimeVal const & from) {
        usrtime += from.usrtime;
        systime += from.systime;
        return *this;
    }

    double getTime() { return usrtime.getTime() + systime.getTime(); }

private:
    BTime usrtime;
    BTime systime;
};

class StopWatch {
public:
    StopWatch(TimeVal & timer) : timer(timer) {
        if (getrusage(RUSAGE_SELF, &tmp_rusage) == 0) {
            time_start = TimeVal(tmp_rusage);
        } else
            assert(false);
    }
    ~StopWatch() {
        if (getrusage(RUSAGE_SELF, &tmp_rusage) == 0) {
            timer += TimeVal(tmp_rusage) - time_start;
        } else
            assert(false);
    }

protected:
    struct rusage tmp_rusage;

    TimeVal time_start;
    TimeVal & timer;
};

class PrintStopWatch {
public:
    PrintStopWatch(char const * _name, std::ostream & os) : os(os), watch(new StopWatch(timer)) {
        int size = strlen(_name);
        name = (char *)malloc(size + 1);
        strcpy(name, _name);
    }
    ~PrintStopWatch() {
        delete watch;
        os << "; " << name << " " << timer.getTime() << " s\n";
        free(name);
    }

protected:
    char * name;
    TimeVal timer;
    std::ostream & os;
    StopWatch * watch;
};
} // namespace opensmt

#endif
