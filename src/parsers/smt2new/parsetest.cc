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


#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <fstream>

#include "smt2newcontext.h"

extern void smt2newset_in       ( FILE * );
extern void smt2newparse        ( );

int main(int argc, char ** argv)
{
    if (argc > 1 && strcmp(argv[1], "--help") == 0) {
        printf("Usage: %s [file]\n", argv[0]); return 1; }

    FILE* in;
    if (argc == 2) {
        if ((in = fopen(argv[1], "r")) == 0) {
            perror("Error opening file"); return 1; }
    }
    else
        in = fopen("/dev/stdin", "r");

    Smt2newContext context(in);
    int rval = smt2newparse(&context);
    printf("Parser returned with result %d and ret val %d\n", context.result, rval);
    if (rval == 0)
        context.prettyPrint(std::cout);
    fclose(in);
    return rval;
}
