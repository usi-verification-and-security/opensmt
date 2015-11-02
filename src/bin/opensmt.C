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


//#include "Egraph.h"
//#include "OpenSMTContext.h"
//#include "SimpSMTSolver.h"
//#include "Tseitin.h"
//#include "ExpandITEs.h"
//#include "ArraySimplify.h"
//#include "BVBooleanize.h"
//#include "TopLevelProp.h"
//#include "DLRescale.h"
//#include "Ackermanize.h"

#include "Interpret.h"
//#include "net/net.h"

#include <cstdlib>
#include <cstdio>
#include <csignal>
#include <iostream>

#if defined(__linux__)
#include <fpu_control.h>
#endif

namespace opensmt {

void        catcher            ( int );
//extern bool stop;

} // namespace opensmt

//extern int  smtset_in          ( FILE * );
//extern int  smtparse           ( );
//extern int  cnfset_in          ( FILE * );
//extern int  cnfparse           ( );
//extern int  smt2set_in         ( FILE * );
//extern int  smt2parse          ( );
//OpenSMTContext * parser_ctx;

/*****************************************************************************\
 *                                                                           *
 *                                  MAIN                                     *
 *                                                                           *
\*****************************************************************************/

int main( int argc, char * argv[] )
{
//  opensmt::stop = false;
  // Allocates Command Handler (since SMT-LIB 2.0)
//  OpenSMTContext context( argc, argv );
  // Catch SigTerm, so that it answers even on ctrl-c
  signal( SIGTERM, opensmt::catcher );
  signal( SIGINT , opensmt::catcher );

  //
  // This trick (copied from Main.C of MiniSAT) is to allow
  // the repeatability of experiments that might be compromised
  // by the floating point unit approximations on doubles
  //
#if defined(__linux__) && !defined( SMTCOMP )
  fpu_control_t oldcw, newcw;
  _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
#endif

#ifdef PEDANTIC_DEBUG
  cerr << "; pedantic assertion checking enabled (very slow)" << endl;
#endif

#ifndef OPTIMIZE
  cerr << "; this binary is compiled with optimizations disabled (slow)" << endl;
#endif

  cerr << "; svn rev: " << SVN_REVISION << endl;

  cerr << "; symbol enode size: " << EnodeAllocator::symEnodeWord32Size() << endl;
  cerr << "; list enode size: " << EnodeAllocator::listEnodeWord32Size() << endl;
  cerr << "; term enode size: " << EnodeAllocator::termEnodeWord32Size() << endl;
  cerr << "; Configured with args " << CONFIG_FLAGS << endl;
  cerr << "; preprocessor definitions set in configure " << CONFIGTIME_DEFFLAGS << endl;
  cerr << "; compiler flags set in configure " << CONFIGTIME_COMPFLAGS << endl;
#ifndef SMTCOMP
//  if ( context.getConfig( ).verbosity > 0 )
  if ( false )
  {
    const int len_pack = strlen( PACKAGE_STRING );
    const char * site = "http://verify.inf.usi.ch/opensmt";
    const int len_site = strlen( site );

    cerr << "#" << endl
         << "# -------------------------------------------------------------------------" << endl
         << "# " << PACKAGE_STRING;

    for ( int i = 0 ; i < 73 - len_site - len_pack ; i ++ )
      cerr << " ";

    cerr << site << endl
         << "# Compiled with gcc " << __VERSION__ << " on " << __DATE__ << endl
         << "# -------------------------------------------------------------------------" << endl
         << "#" << endl;
  }
#endif
  // Initialize pointer to context for parsing
//  parser_ctx    = &context;
  // Accepts file from stdin if nothing specified
    FILE * fin = NULL;
    int opt, i;
//    WorkerClient *w;
    SMTConfig c;
    Interpret interpreter(c);
    while ((opt = getopt(argc, argv, "hs:p:r:")) != -1) {
        switch (opt) {
            case 'p':
                if(!c.sat_split_threads(atoi(optarg))){
                    fprintf(stderr, "Invalid parallel argument: %s\n", optarg);
                    exit(-1);
                }
                break;
            case 's':
                for(i=0;optarg[i]!=':' && optarg[i]!='\0';i++){}
                if(optarg[i]!=':'){
                    fprintf(stderr, "Invalid host:port argument\n");
                    return 1;
                }
                optarg[i]='\0';
                try{
//                    w = new WorkerClient(optarg, atoi(&optarg[i+1]));
//                    w->runForever();
                }catch(char const *s){
                    std::cout << "Exception: " << s << "\n";
                }
                return 0;
            case 'r':
                for(i=0;optarg[i]!=':' && optarg[i]!='\0';i++){}
                if(optarg[i]!=':'){
                    fprintf(stderr, "Invalid host:port argument\n");
                    return 1;
                }
                optarg[i]='\0';
//                NetCfg::server_host=std::string(optarg);
//                NetCfg::server_port=(uint16_t)atoi(&optarg[i+1]);


                break;
            case 'h':
                //    context.getConfig( ).printHelp( );
            default: /* '?' */
                fprintf(stderr, "Usage:\n\t%s [-p threads] filename [...]\n\t%s -s host:port -r host:port\n\t%s -h\n",
                        argv[0], argv[0], argv[0]);
                return 0;
        }
    }
    
  if (argc - optind == 0) {
    fin = stdin;
    int rval = interpreter.interpInteractive(fin);
  }
  else {
    for (int i = optind; i < argc; i++) {
      const char * filename = argv[i];
      assert( filename );
      if ( strncmp( filename, "--", 2 ) == 0
           || strncmp( filename, "-", 1 ) == 0 ) {
        opensmt_error( "input file must be last argument" ); }

      else if ( (fin = fopen( filename, "rt" )) == NULL )
        opensmt_error( "can't open file" );

      const char * extension = strrchr( filename, '.' );
      if ( strcmp( extension, ".smt" ) == 0 ) {
        opensmt_error( "SMTLIB 1.2 format is not supported in this version, sorry" ); }
      else if ( strcmp( extension, ".smt2" ) == 0 ) {
        int rval = interpreter.interpFile(fin);
//      smt2set_in( fin );
//      smt2parse( );
      }
      else
        opensmt_error2( extension, " extension not recognized. Please use one in { smt2, cnf } or stdin (smtlib2 is assumed)" );
    }
    fclose( fin );
  }

  // 
  // Execute accumulated commands
  // function defined in OpenSMTContext.C
  //
//  return context.executeCommands( );
    return 0;
}

namespace opensmt {

void catcher( int sig )
{
  switch (sig)
  {
    case SIGINT:
    case SIGTERM:
        exit(1);
        printf("Exit from signal\n");
//      if ( opensmt::stop )
//      {
//	parser_ctx->PrintResult( l_Undef );
//	exit( 1 );
//      }
//      opensmt::stop = true;
      break;
  }
}

} // namespace opensmt
