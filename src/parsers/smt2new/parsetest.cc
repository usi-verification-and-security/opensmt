/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT -- Copyright (C) 2012 - 2014 Antti Hyvarinen

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
