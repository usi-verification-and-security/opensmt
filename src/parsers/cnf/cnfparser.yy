/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT2 -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

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

%{

#include "Global.h"

#include "Egraph.h"
#include "Anode.h"
#include "OpenSMTContext.h"
#include <cstdio>
#include <cstdlib>
#include <cassert>

extern int cnflineno;
extern int cnflex( );
extern OpenSMTContext * parser_ctx;

void cnferror( const char * s )
{
  printf( "%d: %s \n", cnflineno, s );
  exit( 1 );
}

/* Overallocation to prevent stack overflow */
#define YYMAXDEPTH 1024 * 1024

%}

%union
{
  char  *              str;
  Enode *              enode;
  vector< unsigned > * type_list;
}

%error-verbose

%token TK_P TK_CNF TK_NOT TK_NUM TK_END

%type <str> TK_NUM
%type <enode> formula clause literal literal_list

%start top

%%

top: header formula 
   ;

header: TK_P TK_CNF TK_NUM TK_NUM
	{ 
          const int n_vars = atoi( $3 );
          free( $3 ); free( $4 );
	  int i;
	  vector< unsigned > tmp;
          char buf[ 16 ];
	  for ( i = 1 ; i <= n_vars ; i ++ )
	  {
	    sprintf( buf, "%d", i ); 
	    /*
	    tmp.push_back( DTYPE_BOOL );
	    parser_ctx->newSymbol( buf , tmp );
            */
	    Snode * s = parser_ctx->mkSortBool( );
            parser_ctx->DeclareFun( buf, NULL, s );
	  }
	}
      ;

formula: formula clause
         { parser_ctx->addAssert( $2 ); }
       | clause
         { parser_ctx->addAssert( $1 ); }
       ;

clause: literal_list TK_END
        { $$ = parser_ctx->mkOr( $1 ); }
      ;

literal_list: literal literal_list 
	      { $$ = parser_ctx->mkCons( $1, $2 ); }
            | literal
              { $$ = parser_ctx->mkCons( $1 ); }
            ;

literal: TK_NOT TK_NUM
         { $$ = parser_ctx->mkNot( parser_ctx->mkCons( parser_ctx->mkVar( $2 ) ) ); free( $2 ); } 
       | TK_NUM
         { $$ = parser_ctx->mkVar( $1 ); free( $1 ); } 
       ;

%%
