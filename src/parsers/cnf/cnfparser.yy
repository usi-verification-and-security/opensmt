/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

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
