/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

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

/*********************************************************************
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
of the Software, and to permit persons to whom the Software is furnished to do
so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
**********************************************************************/

#ifndef DimacsParser_h
#define DimacsParser_h

#include <smtsolvers/SimpSMTSolver.h>

#include <cstdlib>
#include <cstdio>
#include <iostream>

namespace opensmt {

class DimacsParser {
    static inline bool isEof(const char*   in) { return *in == '\0'; }

    static void skipWhitespace(const char*& in) {
        while ((*in >= 9 && *in <= 13) || *in == 32)
            ++in; }

    static void skipLine(const char*& in) {
        for (;;){
            if (isEof(in)) return;
            if (*in == '\n') { ++in; return; }
            ++in; } }


    static int parseInt(const char*& in) {
        int     val = 0;
        bool    neg = false;
        skipWhitespace(in);
        if      (*in == '-') neg = true, ++in;
        else if (*in == '+') ++in;
        if (*in < '0' || *in > '9') {
            std::cerr << "PARSE ERROR! Unexpected char: " << *in << std::endl;
            exit(3);
        }
        while (*in >= '0' && *in <= '9')
            val = val*10 + (*in - '0'),
            ++in;
        return neg ? -val : val; }

    // String matching: in case of a match the input iterator will be advanced
    // the corresponding number of characters.
    static bool match(const char*& in, const char* str) {
        int i;
        for (i = 0; str[i] != '\0'; i++)
            if (in[i] != str[i])
                return false;

        in += i;

        return true;
    }

    // String matching: consumes characters eagerly, but does not require
    // random access iterator.
    static bool eagerMatch(const char*& in, const char* str) {
        for (; *str != '\0'; ++str, ++in)
            if (*str != *in)
                return false;
        return true; }

    static void readClause(const char*& in, SimpSMTSolver& S, vec<Lit>& lits) {
        int     parsed_lit, var;
        lits.clear();
        for (;;) {
            parsed_lit = parseInt(in);
            if (parsed_lit == 0) break;
            var = abs(parsed_lit)-1;
            assert(var < S.nVars());
            while (var >= S.nVars()) S.newVar();
            lits.push( (parsed_lit > 0) ? mkLit(var) : ~mkLit(var) );
        }
    }
  public:
    static void parse_DIMACS_main(const char* in, SimpSMTSolver& S) {
        vec<Lit> lits;
        for (;;){
            skipWhitespace(in);
            if (isEof(in))
                break;
            else if (*in == 'p'){
                if (!match(in, "p cnf")) {
                    std::cerr << "PARSE ERROR! Unexpected char: " << *in << endl;
                    exit(3);
                }
            } else if (*in == 'c' || *in == 'p')
                skipLine(in);
            else
                readClause(in, S, lits),
                S.addOriginalClause(lits);
        }
    }
};

}

#endif
