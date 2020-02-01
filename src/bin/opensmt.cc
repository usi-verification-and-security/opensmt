/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso

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


#include "Interpret.h"
#include "Enode.h"

#include <cstdlib>
#include <cstdio>
#include <csignal>
#include <iostream>

#if defined(__linux__)
#include <fpu_control.h>
#endif

namespace opensmt {

void        catcher            ( int );

}

/*****************************************************************************\
 *                                                                           *
 *                                  MAIN                                     *
 *                                                                           *
\*****************************************************************************/

int main( int argc, char * argv[] )
{
    signal( SIGTERM, opensmt::catcher );
    signal( SIGINT , opensmt::catcher );

    //
    // This trick (copied from Main.C of MiniSAT) is to allow
    // the repeatability of experiments that might be compromised
    // by the floating point unit approximations on doubles
    //
#if defined(__linux__)
    fpu_control_t oldcw, newcw;
    _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
#endif

#ifdef PEDANTIC_DEBUG
    cerr << "; pedantic assertion checking enabled (very slow)" << endl;
#endif

#ifndef NDEBUG
    cerr << "; this binary is compiled in debug mode (slow)" << endl;
#endif

    cerr << "; git hash: " << GIT_SHA1 << endl;

  // Accepts file from stdin if nothing specified
    FILE * fin = NULL;
    int opt;

    SMTConfig c;
    while ((opt = getopt(argc, argv, "hdr:")) != -1) {
        switch (opt) {

            case 'h':
                //    context.getConfig( ).printHelp( );
                break;
            case 'd':
                const char* msg;
                c.setOption(SMTConfig::o_dryrun, SMTOption(true), msg);
                break;
            case 'r':
                if (!c.setOption(SMTConfig::o_random_seed, SMTOption(atoi(optarg)), msg))
                    fprintf(stderr, "Error setting random seed: %s\n", msg);
                else
                    fprintf(stderr, "; Using random seed %d\n", atoi(optarg));
                break;
            default: /* '?' */
                fprintf(stderr, "Usage:\n\t%s [-d] [-h] [-r seed] filename [...]\n",
                        argv[0]);
                return 0;
        }
    }

    Interpret interpreter(c);

    if (argc - optind == 0) {
        fin = stdin;
        c.setInstanceName("stdin");
        interpreter.interpInteractive(fin);
    }
    else {
        for (int i = optind; i < argc; i++) {
            const char * filename = argv[i];
            assert( filename );
            c.setInstanceName(filename);
            if ( strncmp( filename, "--", 2 ) == 0
               || strncmp( filename, "-", 1 ) == 0 ) {
                opensmt_error( "input file must be last argument" ); }

            else if ( (fin = fopen( filename, "rt" )) == NULL )
                opensmt_error( "can't open file" );

            const char * extension = strrchr( filename, '.' );
            if ( extension != NULL && strcmp( extension, ".smt" ) == 0 ) {
                opensmt_error( "SMTLIB 1.2 format is not supported in this version, sorry" );
            }
            else if ( extension != NULL && strcmp( extension, ".smt2" ) == 0 ) {
                interpreter.interpFile(fin);
            }
            else
                opensmt_error2( filename, " extension not recognized. Please use one in { smt2, cnf } or stdin (smtlib2 is assumed)" );
        }
        fclose( fin );
    }

    return 0;
}

namespace opensmt {

void catcher( int sig )
{
  switch (sig)
  {
    case SIGINT:
    case SIGTERM:
        printf("Exit from signal\n");
        exit(1);
      break;
  }
}

} // namespace opensmt
