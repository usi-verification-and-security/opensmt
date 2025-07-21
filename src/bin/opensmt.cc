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


#include <api/Interpret.h>

#include <cstdlib>
#include <cstdio>
#include <csignal>
#include <getopt.h>
#include <iostream>
#include <unistd.h>
#include <string>

#define opensmt_error_() 		  { std::cerr << "# Error (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << std::endl; assert(false); ::exit( 1 ); }
#define opensmt_error( S )        { std::cerr << "; Error: " << S << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << std::endl; ::exit( 1 ); }
#define opensmt_error2( S, T )    { std::cerr << "; Error: " << S << " " << T << " (triggered at " <<  __FILE__ << ", " << __LINE__ << ")" << std::endl; ::exit( 1 ); }


#ifdef ENABLE_LINE_EDITING
#include <editline/readline.h>
#endif // ENABLE_LINE_EDITING

#if defined(__GLIBC__)
#include <fpu_control.h>
#endif

namespace opensmt {

using namespace std::string_literals;

namespace {
    bool pipeExecution = false;
}

// Replace this with std::to_underlying once we move to C++23
template<typename Enum>
constexpr std::underlying_type_t<Enum> to_underlying(Enum e) noexcept {
    return static_cast<std::underlying_type_t<Enum>>(e);
}

SMTConfig parseCMDLineArgs(int argc, char * argv[ ]);

void        catcher            ( int );

/*****************************************************************************\
 *                                                                           *
 *                                  MAIN                                     *
 *                                                                           *
\*****************************************************************************/

void interpretInteractive(Interpret & interpret);

}

int main( int argc, char * argv[] )
try {
    using namespace opensmt;

    signal( SIGTERM, catcher );
    signal( SIGINT , catcher );


#ifdef PEDANTIC_DEBUG
    cerr << "; pedantic assertion checking enabled (very slow)" << endl;
#endif

#ifndef NDEBUG
    std::cerr << "; this binary is compiled in debug mode (slow)" << std::endl;
#endif

  // Accepts file from stdin if nothing specified
    FILE * fin = NULL;

    SMTConfig c = parseCMDLineArgs(argc,argv);
    Interpret interpreter(c);

    if (argc - optind == 0) {
        c.setInstanceName("stdin");
        if (pipeExecution) {
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

    int const exit_status = interpreter.okStatus() ? 0 : 1;

    return exit_status;
}
catch (std::exception const & e) {
    std::cerr << "Terminated with exception:\n" << e.what() << std::endl;
    return 1;
}

namespace opensmt {

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
                // Parsing should be done from a string that I get from the editline library.
                Smt2newContext context(parse_buf);
                int rval = osmt_yyparse(&context);
                if (rval != 0)
                    interpret.reportError("scanner");
                else {
                    const ASTNode* r = context.getRoot();
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

void printVersion() { std::cerr << OPENSMT_GIT_DESCRIPTION << "\n"; }


void printHelp()
{
    const char help_string[]
        = "Usage: opensmt [OPTION] <filename>\n"
          "where OPTION can be\n"
          "  --help [-h]                     prints this help message and exits\n"
          "  --version                       prints opensmt version and exits\n"
          "  --verbose [-v]                  verbose run of the solver\n"
          "  --dry-run [-d]                  executes dry run\n"
          "  --random-seed [-r] <seed>       sets random seed to specific number\n"
          "  --produce-models [-m]           enable producing models\n"
          "  --get-models                    get-model after each check-sat gracefully\n"
          "  --produce-unsat-cores           enable producing unsat cores\n"
          "  --get-unsat-cores               get-unsat-core after each check-sat gracefully\n"
          "  --minimal-unsat-cores           produced unsat cores must be irreducible\n"
          "  --print-cores-full              produced unsat cores are agnostic to the smt2 attribute ':named'\n"
          "  --produce-interpolants [-i]     enables interpolant computation\n"
          "  --time-limit [-t] <ms>          sets wall-clock time limit in milliseconds\n"
          "  --pipe [-p]                     for execution within a pipe\n";
    std::cerr << help_string;
}

SMTConfig parseCMDLineArgs( int argc, char * argv[ ] )
{
    enum class LongOpt {
        version,
        getModel,
        produceUcore,
        getUcore,
        minUcore,
        fullUcore,
    };

    SMTConfig res;
    int selectedLongOpt;

    struct option long_options[] =
        {
            {"help", no_argument, nullptr, 'h'},
            {"version", no_argument, &selectedLongOpt, to_underlying(LongOpt::version)},
            {"verbose", no_argument, nullptr, 'v'},
            {"dry-run", no_argument, nullptr, 'd'},
            {"random-seed", required_argument, nullptr, 'r'},
            {"produce-models", no_argument, nullptr, 'm'},
            {"get-models", no_argument, &selectedLongOpt, to_underlying(LongOpt::getModel)},
            {"produce-unsat-cores", no_argument, &selectedLongOpt, to_underlying(LongOpt::produceUcore)},
            {"get-unsat-cores", no_argument, &selectedLongOpt, to_underlying(LongOpt::getUcore)},
            {"minimal-unsat-cores", no_argument, &selectedLongOpt, to_underlying(LongOpt::minUcore)},
            {"print-cores-full", no_argument, &selectedLongOpt, to_underlying(LongOpt::fullUcore)},
            {"produce-interpolants", no_argument, nullptr, 'i'},
            {"time-limit", required_argument, nullptr, 't'},
            {"pipe", no_argument, nullptr, 'p'},
            {0, 0, 0, 0}
        };

    const char* msg;
    bool ok = true;
    while (ok) {
        int option_index = 0;
        int c = getopt_long(argc, argv, "r:hdivpt:", long_options, &option_index);
        if (c == -1) { break; }

        switch (c) {
            case 0:
                switch (LongOpt{*long_options[option_index].flag}) {
                    case LongOpt::version:
                        printVersion();
                        exit(0);
                    case LongOpt::getModel:
                        res.setOption(SMTConfig::o_get_models, SMTOption(true), msg);
                        break;
                    case LongOpt::produceUcore:
                        res.setOption(SMTConfig::o_produce_unsat_cores, SMTOption(true), msg);
                        break;
                    case LongOpt::getUcore:
                        res.setOption(SMTConfig::o_get_unsat_cores, SMTOption(true), msg);
                        break;
                    case LongOpt::minUcore:
                        res.setOption(SMTConfig::o_minimal_unsat_cores, SMTOption(true), msg);
                        break;
                    case LongOpt::fullUcore:
                        res.setOption(SMTConfig::o_print_cores_full, SMTOption(true), msg);
                        break;
                }
                break;
            case 'h':
                printHelp();
                exit(0);
            case 'v':
                res.setOption(SMTConfig::o_verbosity, SMTOption(true), msg);
                break;
            case 'd':
                res.setOption(SMTConfig::o_dryrun, SMTOption(true), msg);
                break;
            case 'r':
                if (!res.setOption(SMTConfig::o_random_seed, SMTOption(atoi(optarg)), msg))
                    fprintf(stderr, "Error setting random seed: %s\n", msg);
                else
                    fprintf(stderr, "; Using random seed %d\n", atoi(optarg));
                break;
            case 'm':
                res.setOption(SMTConfig::o_produce_models, SMTOption(true), msg);
                break;
            case 'i':
                res.setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
                break;
            case 't': {
                int64_t timeLimit;
                try {
                    timeLimit = std::stoll(optarg);
                } catch (std::logic_error const & e) {
                    throw std::invalid_argument{"Invalid argument of time-limit: "s + e.what()};
                }

                ok &= res.setOption(SMTConfig::o_time_limit, SMTOption(timeLimit), msg);
                break;
            }
            case 'p':
                pipeExecution = true;
                break;
            default: /* '?' */
                printHelp();
                exit(1);
        }
    }

    if (not ok) {
        throw std::invalid_argument{"Invalid command-line argument: "s + msg};
    }

    return res;
}

} // namespace opensmt
