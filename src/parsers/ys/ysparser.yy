/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT2 -- Copyright (C) 2008 - 2012 Roberto Bruttomesso

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
#include <cstdio>
#include <cstdlib>
#include <cassert>

extern int yslineno;
extern int yslex( );
extern Egraph *    parser_egraph;
extern SMTConfig * parser_config;

void yserror( char * s )
{
  printf( "%d: %s\n", yslineno, s );
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

%token TK_STR TK_NUM 
%token TK_BOOL TK_INT TK_DEFINE
%token TK_LT TK_EQ TK_LEQ TK_PLUS TK_NEQ TK_MINUS
%token TK_AND TK_OR TK_NOT TK_IF TK_IMPLIES
%token TK_ASSERT TK_EXTASSERT TK_TRUE TK_FALSE TK_CHECK
%token TK_SEPARATOR TK_EVIDENCE TK_RESET TK_SUBRANGE

%type <str> TK_STR TK_NUM
%type <enode> formula atom expression arithmetic_expression
%type <enode> formula_list expression_list arithmetic_expression_list

%start top

%%

top: all
   ;

all: skipped_commands
   | variables_declaration
   | assert_declaration
   | extassert_declaration
   ;

skipped_commands: all evidence
		| all reset
                | all check
                | evidence
		| reset
                | check
	        ;

evidence: '(' TK_EVIDENCE TK_TRUE ')' 
	;

reset: '(' TK_RESET ')' 
     ;

check: '(' TK_CHECK ')' 
     ;

variables_declaration: all bool_variable_declaration
		     | all int_variable_declaration
		     | bool_variable_declaration
		     | int_variable_declaration
                     ;

bool_variable_declaration: '(' TK_DEFINE TK_STR TK_SEPARATOR TK_BOOL ')'
			   { 
		             vector< unsigned > tmp;
		             tmp.push_back( DTYPE_BOOL );
		             parser_egraph->newSymbol( $3, tmp ); free( $3 ); 
			   }
			 ;

int_variable_declaration: '(' TK_DEFINE TK_STR TK_SEPARATOR TK_INT ')'
			  { 
		            vector< unsigned > tmp;
		            tmp.push_back( DTYPE_INT );
		            parser_egraph->newSymbol( $3, tmp ); free( $3 ); 
			  }
			| '(' TK_DEFINE TK_STR TK_SEPARATOR '(' TK_SUBRANGE TK_NUM TK_NUM ')' ')'
			  {
		            vector< unsigned > tmp;
		            tmp.push_back( DTYPE_INT );
		            parser_egraph->newSymbol( $3, tmp );
		            Enode * x  = parser_egraph->mkVar( $3 ); free( $3 ); 
			    Enode * r1 = parser_egraph->mkNum( $7 ); free( $7 );
			    Enode * r2 = parser_egraph->mkNum( $8 ); free( $8 );
			    Enode * leq1 = parser_egraph->mkLeq( parser_egraph->cons( r1, parser_egraph->cons( x ) ) );
			    Enode * leq2 = parser_egraph->mkLeq( parser_egraph->cons( x , parser_egraph->cons( r2 ) ) );
			    Enode * conj  = parser_egraph->mkAnd( parser_egraph->cons( leq1, parser_egraph->cons( leq2 ) ) );
			    parser_egraph->addAssumption( conj );
			  }
			;

assert_declaration: all '(' TK_ASSERT formula ')'
		    { parser_egraph->addAssumption( $4 ); }
		  | '(' TK_ASSERT formula ')'
		    { parser_egraph->addAssumption( $3 ); }
		  ;

extassert_declaration: all '(' TK_EXTASSERT formula ')'
		       { parser_egraph->addAssumption( $4 ); }
		     | '(' TK_EXTASSERT formula ')'
		       { parser_egraph->addAssumption( $3 ); }
		     ;

formula: '(' TK_AND formula_list ')' 
	 { $$ = parser_egraph->mkAnd( $3 ); } 
       | '(' TK_OR formula_list ')'
	 { $$ = parser_egraph->mkOr( $3 ); } 
       | '(' TK_IF formula_list ')'
	 { $$ = parser_egraph->mkImplies( $3 ); } 
       | '(' TK_NOT formula_list ')'
	 { $$ = parser_egraph->mkNot( $3 ); }
       | '(' TK_IMPLIES formula_list ')'
	 { $$ = parser_egraph->mkImplies( $3 ); }
       | atom
	 { $$ = $1; }
       ;

formula_list: formula formula_list
	      { $$ = parser_egraph->cons( $1, $2 ); }
	    | formula
	      { $$ = parser_egraph->cons( $1 ); }   
	    ;

atom: '(' TK_LT arithmetic_expression_list ')'
      { $$ = parser_egraph->mkLt( $3 ); }
    | '(' TK_LEQ expression_list ')'
      { $$ = parser_egraph->mkLeq( $3 ); }
    | '(' TK_EQ expression_list ')'
      { $$ = parser_egraph->mkEq( $3 ); }
    | '(' TK_NEQ expression_list ')'
      { $$ = parser_egraph->mkNeq( $3 ); }
    | TK_STR
      { $$ = parser_egraph->mkVar( $1 ); free( $1 ); }
    | TK_TRUE
      { $$ = parser_egraph->mkTrue( ); }
    | TK_FALSE
      { $$ = parser_egraph->mkFalse( ); }
    ;

expression: arithmetic_expression 
	    { $$ = $1; }
	  | formula
	    { $$ = $1; }
	  ;

expression_list: expression expression_list
	         { $$ = parser_egraph->cons( $1, $2 ); }
	       | expression
		 { $$ = parser_egraph->cons( $1 ); }   
               ;

arithmetic_expression: '(' TK_PLUS arithmetic_expression_list ')' 
		       { $$ = parser_egraph->mkPlus( $3 ); }
		     | '(' TK_MINUS arithmetic_expression_list ')' 
		       { $$ = parser_egraph->mkPlus( $3 ); }
                     | TK_NUM
                       { $$ = parser_egraph->mkNum( $1 ); free( $1 ); }
                     | TK_STR
                       { $$ = parser_egraph->mkVar( $1 ); free( $1 ); }
                     ;

arithmetic_expression_list: arithmetic_expression arithmetic_expression_list
	                    { $$ = parser_egraph->cons( $1, $2 ); }
			  | arithmetic_expression
		            { $$ = parser_egraph->cons( $1 ); }   
                          ;

%%
