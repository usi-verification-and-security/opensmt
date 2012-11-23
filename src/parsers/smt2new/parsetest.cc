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
