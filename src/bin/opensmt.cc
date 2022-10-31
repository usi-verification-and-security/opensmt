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

#include <cstdlib>
#include <cstdio>
#include <csignal>
#include <iostream>
#include <unistd.h>

#define opensmt_error_() 		  { std::cerr << "# Error (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << std::endl; assert(false); ::exit( 1 ); }
#define opensmt_error( S )        { std::cerr << "; Error: " << S << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << std::endl; ::exit( 1 ); }
#define opensmt_error2( S, T )    { std::cerr << "; Error: " << S << " " << T << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << std::endl; ::exit( 1 ); }


#ifdef ENABLE_LINE_EDITING
#if !defined(USE_READLINE)
#include <editline/readline.h>
#else
#include <readline/readline.h>
#include <readline/history.h>
#endif
#endif // ENABLE_LINE_EDITING

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

void interpretInteractive(Interpret & interpret);

int main( int argc, char * argv[] )
{
    signal( SIGTERM, opensmt::catcher );
    signal( SIGINT , opensmt::catcher );
    

#ifdef PEDANTIC_DEBUG
    cerr << "; pedantic assertion checking enabled (very slow)" << endl;
#endif

#ifndef NDEBUG
    std::cerr << "; this binary is compiled in debug mode (slow)" << std::endl;
#endif

  // Accepts file from stdin if nothing specified
    FILE * fin = NULL;
    int opt;

    SMTConfig c;
    bool pipe = false;
    while ((opt = getopt(argc, argv, "hdpir:v")) != -1) {
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
            case 'i':
                c.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
                break;
            case 'v':
                c.setOption(SMTConfig::o_verbosity, SMTOption(true), msg);
                break;
            case 'p':
                pipe = true;
                break;
            default: /* '?' */
                fprintf(stderr, "Usage:\n\t%s [-d] [-h] [-r seed] filename [...]\n",
                        argv[0]);
                return 0;
        }
    }

    Interpret interpreter(c);

    if (argc - optind == 0) {
        c.setInstanceName("stdin");
        if (pipe) {
            interpreter.interpPipe();
        }
        else {
            interpretInteractive(interpreter);
        }
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

#ifndef ENABLE_LINE_EDITING
void interpretInteractive(Interpret & interpret) {
    interpret.interpPipe();
}
#else
void interpretInteractive(Interpret & interpret) {
    char* line_read = nullptr;
    bool done = false;
    int par = 0;
    int pb_cap = 1;
    int pb_sz = 0;
    char *parse_buf = (char *) malloc(pb_cap);

    while (!done) {
        if (line_read) {
            free(line_read);
            line_read = nullptr;
        }
        if (par == 0)
            line_read = readline("> ");
        else if (par > 0)
            line_read = readline("... ");
        else {
            interpret.reportError("interactive reader: unbalanced parentheses");
            parse_buf[pb_sz-1] = 0; // replace newline with end of string
            add_history(parse_buf);
            pb_sz = 0;
            par = 0;
        }

        if (line_read && *line_read) {
            for (int i = 0; line_read[i] != '\0'; i++) {
                char c = line_read[i];
                if (c == '(') par ++;
                if (c == ')') par --;
                while (pb_cap - 2 < pb_sz) { // the next char and terminating zero
                    pb_cap *= 2;
                    parse_buf = (char*) realloc(parse_buf, pb_cap);
                }
                parse_buf[pb_sz ++] = c;
            }
            if (par == 0) {
                parse_buf[pb_sz] = '\0';
                // Parse starting from the command nonterminal
                // Parsing should be done from a string that I get from the readline
                // library.
                Smt2newContext context(parse_buf);
                int rval = yyparse(&context);
                if (rval != 0)
                    interpret.reportError("scanner");
                else {
                    ASTNode const & r = context.getRoot();
                    interpret.execute(r);
                    done = interpret.gotExit();
                }
                add_history(parse_buf);
                pb_sz = 0;
            }
            else { // add the line break
                while (pb_cap - 2 < pb_sz) { // the next char and terminating zero
                    pb_cap *= 2;
                    parse_buf = (char*) realloc(parse_buf, pb_cap);
                }
                parse_buf[pb_sz ++] = '\n';
            }
        }
    }
    if (parse_buf) free(parse_buf);
    if (line_read) free(line_read);
}
#endif

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
