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

%{

#include "Global.h"

#include "Egraph.h"
#include "ANode.h"
#include "OpenSMTContext.h"
#include <cstdio>
#include <cstdlib>
#include <cassert>

extern int smtlineno;
extern int smtlex( );
extern OpenSMTContext * parser_ctx;

vector< unsigned > * createTypeList  ( unsigned );
vector< unsigned > * createTypeList  ( unsigned, const char * );
vector< unsigned > * pushTypeList    ( vector< unsigned > *, unsigned );
vector< unsigned > * pushTypeList    ( vector< unsigned > *, unsigned, const char * );
void		     destroyTypeList ( vector< unsigned > * );

void smterror( const char * s )
{
  printf( "%d: %s \n", smtlineno, s );
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

%token TK_NUM TK_STR TK_BVNUM TK_BVNUM_NO_WIDTH TK_BIT0 TK_BIT1
%token TK_REAL TK_INT TK_BITVEC TK_U TK_ARRAY TK_ARRAY_INDEX TK_ARRAY_ELEMENT
%token TK_PLUS TK_MINUS TK_TIMES TK_UMINUS TK_DIV
%token TK_NE TK_EQ TK_LEQ TK_GEQ TK_LT TK_GT
%token TK_AND TK_OR TK_NOT TK_IFF TK_XOR TK_ITE TK_IFTHENELSE TK_IMPLIES
%token TK_BENCHMARK TK_SOURCE TK_ARGUMENT TK_STATUS TK_NOTES
%token TK_EXTRASORTS TK_EXTRAPREDS TK_EXTRAFUNS TK_LOGIC TK_CATEGORY TK_DIFFICULTY
%token TK_ASSUMPTION TK_FORMULA TK_TRUE TK_FALSE TK_INTERPOLATE
%token TK_FLET TK_FLET_STR TK_LET TK_LET_STR TK_DISTINCT
%token TK_BVSLT TK_BVSGT TK_BVSLE TK_BVSGE
%token TK_BVULT TK_BVUGT TK_BVULE TK_BVUGE
%token TK_EXTRACT TK_CONCAT TK_BVAND TK_BVOR TK_BVXOR TK_BVNOT TK_BVADD TK_BVNEG TK_BVMUL TK_BVASHR TK_REPEAT
%token TK_SIGN_EXTEND TK_ZERO_EXTEND TK_ROTATE_LEFT TK_ROTATE_RIGHT TK_BVLSHR TK_BVSHL TK_BVSREM TK_BVSDIV TK_BVSUB
%token TK_BVUDIV TK_BVUREM
%token TK_ARRAY_SELECT TK_ARRAY_STORE

%type <str> TK_STR TK_NUM TK_BVNUM TK_BVNUM_NO_WIDTH TK_ARGUMENT TK_REAL TK_INT TK_FLET_STR TK_LET_STR
%type <enode> formula atom expression arithmetic_expression bitvec_expression 
%type <enode> array_expression array_element_expression array_index_expression array_element_expression_list
%type <enode> array_bitvec_expression_list
%type <enode> formula_list expression_list arithmetic_expression_list bitvec_expression_list
%type <type_list> type_list

%start top

%%

top: '(' all ')'
   ;

all: all header_declaration
   | all variables_declaration
   | all assumption_declaration
   | all formula_declaration
   | all formula_n_declaration
   | header_declaration
   | variables_declaration
   | assumption_declaration
   | formula_declaration
   | formula_n_declaration
   ;

header_declaration: header_declaration benchmark_declaration
		  | header_declaration notes_declaration
		  | header_declaration source_declaration 
                  | header_declaration status_declaration
                  | header_declaration category_declaration
		  | header_declaration difficulty_declaration
		  | header_declaration logic_declaration
		  | header_declaration interpolation_declaration
                  | benchmark_declaration
                  | notes_declaration
                  | source_declaration
                  | status_declaration
                  | category_declaration
                  | difficulty_declaration
                  | logic_declaration
                  | interpolation_declaration
		  ;

benchmark_declaration: TK_BENCHMARK TK_STR
		       { free( $2 ); }
		     ;

interpolation_declaration: TK_INTERPOLATE TK_NUM
			   {  }
                         ;

notes_declaration: TK_NOTES TK_ARGUMENT
		   { free( $2 ); }
		 ;

source_declaration: TK_SOURCE TK_ARGUMENT
		    { free( $2 ); }
		  ;

status_declaration: TK_STATUS TK_STR
		    { 
		      assert( false );
                      parser_ctx->SetInfo( NULL );
		      free( $2 ); 
		    }
		  ;

category_declaration: TK_CATEGORY TK_ARGUMENT
		      { free( $2 ); }
		    ;

difficulty_declaration: TK_DIFFICULTY TK_ARGUMENT
		        { free( $2 ); }
		      ;

logic_declaration: TK_LOGIC TK_STR
		   { 
		    /*
                          if ( strcmp( $2, "EMPTY" ) == 0 ) parser_config->logic = EMPTY;
                     else if ( strcmp( $2, "QF_UF" ) == 0 ) parser_config->logic = QF_UF;
                     else if ( strcmp( $2, "QF_BV" ) == 0 ) parser_config->logic = QF_BV;
                     else if ( strcmp( $2, "QF_RDL" ) == 0 ) parser_config->logic = QF_RDL;
                     else if ( strcmp( $2, "QF_IDL" ) == 0 ) parser_config->logic = QF_IDL;
                     else if ( strcmp( $2, "QF_LRA" ) == 0 ) parser_config->logic = QF_LRA;
                     else if ( strcmp( $2, "QF_LIA" ) == 0 ) parser_config->logic = QF_LIA;
                     else if ( strcmp( $2, "QF_UFRDL" ) == 0 ) 
                     {
                       parser_config->logic = QF_UFRDL;
                       parser_config->incremental |= parser_config->satconfig.lazy_dtc != 0;
                     }
                     else if ( strcmp( $2, "QF_UFIDL" ) == 0 ) 
		     {
                       parser_config->logic = QF_UFIDL;
                       parser_config->incremental |= parser_config->satconfig.lazy_dtc != 0;
                     }
                     else if ( strcmp( $2, "QF_UFLRA" ) == 0 ) 
		     { 
                       parser_config->logic = QF_UFLRA; 
                       parser_config->lraconfig.gaussian_elim = parser_config->satconfig.lazy_dtc == 0; 
                       parser_config->incremental |= parser_config->satconfig.lazy_dtc != 0;
		     }
                     else if ( strcmp( $2, "QF_UFLIA" ) == 0 ) 
		     {
		       parser_config->logic = QF_UFLIA;
                       parser_config->incremental |= parser_config->satconfig.lazy_dtc != 0;
		     }
                     else if ( strcmp( $2, "QF_UFBV" ) == 0 ) parser_config->logic = QF_UFBV;
		     else if ( strcmp( $2, "QF_AX" ) == 0 ) 
		     { 
		       parser_config->logic = QF_AX;	
		       parser_config->incremental = 1;
		     }
                     else if ( strcmp( $2, "QF_AUFBV" ) == 0 ) parser_config->logic = QF_AUFBV;
// DO NOT REMOVE THIS COMMENT !!
// IT IS USED BY CREATE_THEORY.SH SCRIPT !!
// NEW_THEORY_INIT
		     parser_egraph->initializeStore( );
                    */
                     parser_ctx->SetLogic( $2 );
		     free( $2 ); 
                   }
		 ;

variables_declaration: variables_declaration bool_variable_declaration
		     | variables_declaration real_variable_declaration
		     | variables_declaration int_variable_declaration
		     | variables_declaration bitvec_variable_declaration
		     | variables_declaration u_function_declaration
		     | variables_declaration u_predicate_declaration
		     | variables_declaration arrayrelated_variable_declaration 	
                     | sort_declaration
		     | bool_variable_declaration
		     | real_variable_declaration
		     | int_variable_declaration
		     | bitvec_variable_declaration
		     | u_function_declaration
		     | u_predicate_declaration
		     | arrayrelated_variable_declaration
                     ;

sort_declaration: TK_EXTRASORTS '(' TK_STR ')'
		  { 
/* 
                    parser_egraph->newSort( $3 ); 
		    free( $3 ); 
*/
                  }

bool_variable_declaration: TK_EXTRAPREDS '(' bool_variable_list ')'
			 ;

bool_variable_list: bool_variable_list '(' TK_STR ')'
		    { 
                      /*
		      vector< unsigned > tmp;
		      tmp.push_back( DTYPE_BOOL );
		      parser_egraph->newSymbol( $3, tmp ); free( $3 ); 
		      Snode * s = parser_ctx->mkSortBool( );
		      parser_ctx->DeclareFun( $3, s ); free( $3 ); 
                      */
		    }
		  | '(' TK_STR ')'
		    { 
                      /*
		      vector< unsigned > tmp;
		      tmp.push_back( DTYPE_BOOL );
		      parser_egraph->newSymbol( $2, tmp ); free( $2 ); 
		      Snode * s = parser_ctx->mkSortBool( );
		      parser_ctx->DeclareFun( $2, s ); free( $2 ); 
                      */
		    }
                  ;
		     
real_variable_declaration: TK_EXTRAFUNS '(' real_variable_list ')'
			 ;

real_variable_list: real_variable_list '(' TK_STR TK_REAL ')'
		    { 
                      /*
		      vector< unsigned > tmp;
		      tmp.push_back( DTYPE_REAL );
		      parser_egraph->newSymbol( $3, tmp ); free( $3 ); 
		      Snode * s = parser_ctx->mkSortReal( );
		      parser_ctx->DeclareFun( $3, s ); free( $3 ); 
                      */
		    }
		  | '(' TK_STR TK_REAL ')'
		    { 
                      /*
		      vector< unsigned > tmp;
		      tmp.push_back( DTYPE_REAL );
		      parser_egraph->newSymbol( $2, tmp ); free( $2 ); 
		      Snode * s = parser_ctx->mkSortReal( );
		      parser_ctx->DeclareFun( $2, s ); free( $2 ); 
                      */
		    }
                  ;

int_variable_declaration: TK_EXTRAFUNS '(' int_variable_list ')'
			;

int_variable_list: int_variable_list '(' TK_STR TK_INT ')'
		   { 
                     /*
		     vector< unsigned > tmp;
		     tmp.push_back( DTYPE_INT );
		     parser_egraph->newSymbol( $3, tmp ); free( $3 ); 
		     Snode * s = parser_ctx->mkSortInt( );
		     parser_ctx->DeclareFun( $3, s ); free( $3 ); 
                     */
                   }
		  | '(' TK_STR TK_INT ')'
		   { 
                     /*
		     vector< unsigned > tmp;
		     tmp.push_back( DTYPE_INT );
		     parser_egraph->newSymbol( $2, tmp ); free( $2 ); 
		     Snode * s = parser_ctx->mkSortInt( );
		     parser_ctx->DeclareFun( $2, s ); free( $2 ); 
                     */
		   }
                  ;

bitvec_variable_declaration: TK_EXTRAFUNS '(' bitvec_variable_list ')'
			   ;

bitvec_variable_list: bitvec_variable_list '(' TK_STR TK_BITVEC '[' TK_NUM ']' ')'
		      { 
/*
			if ( atoi( $6 ) > MAX_WIDTH ) error( "bitvector width too large, max is ", MAX_WIDTH );
			vector< unsigned > tmp;
			tmp.push_back( DTYPE_BITVEC | atoi( $6 ) );
			parser_egraph->newSymbol( $3, tmp ); free( $3 ); free( $6 ); 
*/
		      }
		    | '(' TK_STR  TK_BITVEC '[' TK_NUM ']' ')'
		      { 
/*
			if ( atoi( $5 ) > MAX_WIDTH ) error( "bitvector width too large, max is ", MAX_WIDTH );
			vector< unsigned > tmp;
			tmp.push_back( DTYPE_BITVEC | atoi( $5 ) );
			parser_egraph->newSymbol( $2, tmp ); free( $2 ); free( $5 ); 
*/
		      }
                    ;

arrayrelated_variable_declaration: array_variable_declaration
		 	     | array_index_variable_declaration		
		             | array_element_variable_declaration
			     ; 

array_variable_declaration: TK_EXTRAFUNS '(' array_variable_list ')'
			  ;

array_index_variable_declaration: TK_EXTRAFUNS '(' array_index_variable_list ')'
			  ;

array_element_variable_declaration: TK_EXTRAFUNS '(' array_element_variable_list ')'
			  ;

array_variable_list: array_variable_list '(' TK_STR TK_ARRAY ')'
		     {
                      /*
		      vector< unsigned > tmp;
		      tmp.push_back( DTYPE_ARRAY );
		      parser_egraph->newSymbol( $3, tmp ); free( $3 );
		      Snode * s = parser_ctx->mkSortArray( );
		      parser_ctx->DeclareFun( $3, s ); free( $3 ); 
                      */
		     }
		   | '(' TK_STR TK_ARRAY ')'
		     {
                      /*
		      vector< unsigned > tmp;
		      tmp.push_back( DTYPE_ARRAY );
		      parser_egraph->newSymbol( $2, tmp ); free( $2 ); 
		      Snode * s = parser_ctx->mkSortArray( );
		      parser_ctx->DeclareFun( $2, s ); free( $2 ); 
                      */
		     }	
		   | '(' TK_STR TK_ARRAY '[' TK_NUM ':' TK_NUM ']' ')'
		     {
                      /*
		      vector< unsigned > tmp;
		      tmp.push_back( DTYPE_ARRAY | atoi( $7 ) );
		      parser_egraph->newSymbol( $2, tmp ); free( $2 ); 
		      Snode * s = parser_ctx->mkSortArray( );
		      parser_ctx->DeclareFun( $2, s ); free( $2 ); 
                      */
		     }	
		   ;

array_index_variable_list: array_index_variable_list '(' TK_STR TK_ARRAY_INDEX ')'
                           {
/*
		            vector< unsigned > tmp;
		            tmp.push_back( DTYPE_ARRAY_INDEX );
		            parser_egraph->newSymbol( $3, tmp ); free( $3 );
*/
			   }
			 | '(' TK_STR TK_ARRAY_INDEX ')'
                           {
/*
		            vector< unsigned > tmp;
		            tmp.push_back( DTYPE_ARRAY_INDEX );
		            parser_egraph->newSymbol( $2, tmp ); free( $2 );
*/
			   }

array_element_variable_list: array_element_variable_list '(' TK_STR TK_ARRAY_ELEMENT ')'
			     {
/*
			      vector< unsigned > tmp;
		              tmp.push_back( DTYPE_ARRAY_ELEMENT );
		              parser_egraph->newSymbol( $3, tmp ); free( $3 );
*/
			     }
			   | '(' TK_STR TK_ARRAY_ELEMENT ')'
			     {
/*
			      vector< unsigned > tmp;
		              tmp.push_back( DTYPE_ARRAY_ELEMENT );
		              parser_egraph->newSymbol( $2, tmp ); free( $2 );
*/
		 	     }

u_predicate_declaration: TK_EXTRAPREDS '(' u_predicate_list ')'
		      ;

u_predicate_list: u_predicate_list '(' TK_STR type_list ')'
	         { 
/*
		   (*$4).push_back( DTYPE_BOOL ); 
                   parser_egraph->newSymbol( $3, (*$4) ); 
		   free( $3 ); 
		   destroyTypeList( $4 ); 
*/
                 }
               | '(' TK_STR type_list ')'
                 { 
/*
		   (*$3).push_back( DTYPE_BOOL ); 
		   parser_egraph->newSymbol( $2, (*$3) ); 
                   free( $2 ); 
                   destroyTypeList( $3 ); 
*/
                 }
	       ;

u_function_declaration: TK_EXTRAFUNS '(' u_function_list ')'
		      ;

u_function_list: u_function_list '(' TK_STR type_list ')'
	         { 
/*
                   parser_egraph->newSymbol( $3, (*$4) ); 
                   free( $3 ); 
                   destroyTypeList( $4 ); 
*/
                 }
               | '(' TK_STR type_list ')'
                 { 
/*
                   parser_egraph->newSymbol( $2, (*$3) ); 
                   free( $2 ); 
                   destroyTypeList( $3 ); 
*/
                 }
	       ;

type_list: type_list TK_U
	 /*
	  { $$ = pushTypeList( $1, DTYPE_U ); }
	| type_list TK_INT
	  { $$ = pushTypeList( $1, DTYPE_INT ); }
	| type_list TK_REAL
	  { $$ = pushTypeList( $1, DTYPE_REAL ); }
	| type_list TK_BITVEC '[' TK_NUM ']'
	  { $$ = pushTypeList( $1, DTYPE_BITVEC, $4 ); free( $4 ); }
	| type_list TK_ARRAY
	  { $$ = pushTypeList( $1, DTYPE_ARRAY ); }
	| type_list TK_ARRAY_INDEX
	  { $$ = pushTypeList( $1, DTYPE_ARRAY_INDEX ); }
	| type_list TK_ARRAY_ELEMENT
	  { $$ = pushTypeList( $1, DTYPE_ARRAY_ELEMENT ); }
	| type_list TK_STR
	  { $$ = pushTypeList( $1, parser_egraph->getSort( $2 ) ); free( $2 ); }
	| TK_U
          { $$ = createTypeList( DTYPE_U ); }
	| TK_INT
          { $$ = createTypeList( DTYPE_INT ); }
	| TK_REAL
          { $$ = createTypeList( DTYPE_REAL ); }
	| TK_BITVEC '[' TK_NUM ']'
          { $$ = createTypeList( DTYPE_BITVEC, $3 ); free( $3 ); }
	| TK_ARRAY
	  { $$ = createTypeList( DTYPE_ARRAY ); }
	| TK_ARRAY_INDEX
	  { $$ = createTypeList( DTYPE_ARRAY_INDEX ); }
	| TK_ARRAY_ELEMENT
	  { $$ = createTypeList( DTYPE_ARRAY_ELEMENT ); }
	| TK_STR
          { $$ = createTypeList( parser_egraph->getSort( $1 ) ); free( $1 ); }
*/
	;

assumption_declaration: assumption_declaration TK_ASSUMPTION formula
			{ parser_ctx->addAssert( $3 ); }
		      | TK_ASSUMPTION formula
		        { parser_ctx->addAssert( $2 ); }
		      ;

formula_declaration: TK_FORMULA formula
		     { /*parser_egraph->setTopEnode( $2 );*/ }
		   ;

formula_n_declaration: TK_FORMULA TK_NUM
		       { 
#ifdef PRODUCE_PROOF
			 /*parser_egraph->addIFormula( ); */
#endif
                       }
		     ;

formula: '(' TK_AND formula_list ')' 
	 { $$ = parser_ctx->mkAnd( $3 ); } 
       | '(' TK_OR formula_list ')'
	 { $$ = parser_ctx->mkOr( $3 ); } 
       | '(' TK_IMPLIES formula_list ')'
	 { $$ = parser_ctx->mkImplies( $3 ); } 
       | '(' TK_NOT formula_list ')'
	 { $$ = parser_ctx->mkNot( $3 ); }
       | '(' TK_IFF formula_list ')'
         { /*$$ = parser_ctx->mkIff( $3 );*/ }
       | '(' TK_XOR formula_list ')'
         { $$ = parser_ctx->mkXor( $3 ); }
       | '(' TK_IFTHENELSE formula formula formula ')'
         { /*$$ = parser_egraph->mkIfthenelse( $3, $4, $5 );*/ }
       | '(' TK_FLET flet_def formula ')'
         { $$ = $4; }
       | '(' TK_LET let_def formula ')'
	 { $$ = $4; }
       | TK_FLET_STR
         { /*$$ = parser_egraph->getDefine( $1 ); free( $1 );*/ }
       | atom
	 { $$ = $1; }
       ;

formula_list: formula formula_list
	      { $$ = parser_ctx->mkCons( $1, $2 ); }
	    | formula
	      { $$ = parser_ctx->mkCons( $1 ); }   
	    ;

let_def: '(' TK_LET_STR expression ')'
	 { /*parser_ctx->mkDefine( $2, $3 ); free( $2 );*/ } 

flet_def: '(' TK_FLET_STR formula ')'
	  { /*parser_ctx->mkDefine( $2, $3 ); free( $2 );*/ } 

atom: '(' TK_GEQ arithmetic_expression_list ')'
      { $$ = parser_ctx->mkGeq( $3 ); }
    | '(' TK_LEQ arithmetic_expression_list ')'
      { $$ = parser_ctx->mkLeq( $3 ); }
    | '(' TK_GT arithmetic_expression_list ')'
      { $$ = parser_ctx->mkGt( $3 ); }
    | '(' TK_LT arithmetic_expression_list ')'
      { $$ = parser_ctx->mkLt( $3 ); }
/*
    | '(' TK_BVSLT bitvec_expression_list ')'
      { $$ = parser_egraph->mkBvslt( $3 ); }
    | '(' TK_BVSGT bitvec_expression_list ')'
      { $$ = parser_egraph->mkBvsgt( $3 ); }
    | '(' TK_BVSLE bitvec_expression_list ')'
      { $$ = parser_egraph->mkBvsle( $3 ); }
    | '(' TK_BVSGE bitvec_expression_list ')'
      { $$ = parser_egraph->mkBvsge( $3 ); }
    | '(' TK_BVULT bitvec_expression_list ')'
      { $$ = parser_egraph->mkBvult( $3 ); }
    | '(' TK_BVUGT bitvec_expression_list ')'
      { $$ = parser_egraph->mkBvugt( $3 ); }
    | '(' TK_BVULE bitvec_expression_list ')'
      { $$ = parser_egraph->mkBvule( $3 ); }
    | '(' TK_BVUGE bitvec_expression_list ')'
      { $$ = parser_egraph->mkBvuge( $3 ); }
*/
    | '(' TK_EQ expression_list ')'
      { $$ = parser_ctx->mkEq( $3 ); }
    | '(' TK_DISTINCT expression_list ')'
      { $$ = parser_ctx->mkDistinct( $3 ); }
    | TK_STR
      { $$ = parser_ctx->mkVar( $1, true ); free( $1 ); }
    | TK_TRUE
      { $$ = parser_ctx->mkTrue( ); }
    | TK_FALSE
      { $$ = parser_ctx->mkFalse( ); }
    | '(' TK_STR expression_list ')'
      { /*$$ = parser_ctx->mkUp( $2, $3 ); free( $2 );*/ }
    ;

expression: arithmetic_expression 
	    { $$ = $1; }
	  | bitvec_expression 
            { $$ = $1; }
	  | array_expression
	    { $$ = $1; }
	  | array_element_expression
	    { $$ = $1; }
	  | array_index_expression
	    { $$ = $1; }
	  | '(' TK_STR expression_list ')'
	    { /*$$ = parser_egraph->mkUf( $2, $3 ); free( $2 );*/ }
	  ;

expression_list: expression expression_list
	         { $$ = parser_ctx->mkCons( $1, $2 ); }
	       | expression
		 { $$ = parser_ctx->mkCons( $1 ); }   
               ;

arithmetic_expression: '(' TK_PLUS arithmetic_expression_list ')' 
		       { $$ = parser_ctx->mkPlus( $3 ); }
		     | '(' TK_MINUS arithmetic_expression_list ')'
		       { $$ = parser_ctx->mkMinus( $3 ); }
                     | '(' TK_TIMES arithmetic_expression_list ')'
		       { $$ = parser_ctx->mkTimes( $3 ); }
                     | '(' TK_UMINUS arithmetic_expression_list ')'
                       { $$ = parser_ctx->mkUminus( $3 ); }
                     | '(' TK_DIV TK_NUM TK_NUM ')'
                       { /*$$ = parser_ctx->mkNum( $3, $4 ); free( $3 ); free( $4 );*/ }
                     | '(' TK_DIV arithmetic_expression_list ')'
                       { $$ = parser_ctx->mkDiv( $3 ); }
                     | TK_NUM
                       { $$ = parser_ctx->mkNum( $1 ); free( $1 ); }
                     | TK_STR
                       { $$ = parser_ctx->mkVar( $1, true ); free( $1 ); }
	             | TK_LET_STR
	               { /*$$ = parser_ctx->getDefine( $1 ); free( $1 );*/ }
	             | '(' TK_ITE formula arithmetic_expression arithmetic_expression ')'
	               { /*$$ = parser_ctx->mkIte( $3, $4, $5 );*/ }
	             | '(' TK_STR expression_list ')'
	               { /*$$ = parser_ctx->mkUf( $2, $3 ); free( $2 );*/ }
                     ;

arithmetic_expression_list: arithmetic_expression arithmetic_expression_list
			  /*
	                    { $$ = parser_ctx->cons( $1, $2 ); }
			  | arithmetic_expression
		            { $$ = parser_ctx->cons( $1 ); }   
                          */
                          ;

bitvec_expression: '(' TK_CONCAT bitvec_expression_list ')'
		   { $$ = NULL; }
/*
		   { $$ = parser_egraph->mkConcat( $3 ); }
                 | '(' TK_CONCAT array_element_expression_list ')'
		   { $$ = parser_egraph->mkConcat( $3 ); }
                 | '(' TK_CONCAT array_bitvec_expression_list ')'
		   { $$ = parser_egraph->mkConcat( $3 ); }
                 | '(' TK_EXTRACT '[' TK_NUM ':' TK_NUM ']' TK_BVNUM_NO_WIDTH ')'
		   { 
		     char tmp[ 256 ]; 
		     sprintf( tmp, "%s[%d]", $8, atoi( $4 ) - atoi( $6 ) + 1 ); 
		     $$ = parser_egraph->mkBvnum( tmp ); 
		     free( $4 ); free( $6 ); free( $8 ); 
		   }
                 | '(' TK_EXTRACT '[' TK_NUM ':' TK_NUM ']' bitvec_expression ')'
                   { $$ = parser_egraph->mkExtract( atoi( $4 ), atoi( $6 ), $8 ); free( $4 ); free( $6 ); } 
                 | '(' TK_REPEAT '[' TK_NUM ']' bitvec_expression ')'
                   { $$ = parser_egraph->mkRepeat( atoi( $4 ), $6 ); }
                 | '(' TK_BVAND bitvec_expression_list ')'
		   { $$ = parser_egraph->mkBvand( $3 ); }
                 | '(' TK_BVOR bitvec_expression_list ')'
		   { $$ = parser_egraph->mkBvor( $3 ); }
                 | '(' TK_BVXOR bitvec_expression_list ')'
		   { $$ = parser_egraph->mkBvxor( $3 ); }
                 | '(' TK_BVNOT bitvec_expression_list ')'
		   { $$ = parser_egraph->mkBvnot( $3 ); }
                 | '(' TK_BVADD bitvec_expression_list ')'
		   { $$ = parser_egraph->mkBvadd( $3 ); }
                 | '(' TK_BVSUB bitvec_expression_list ')'
		   { $$ = parser_egraph->mkBvsub( $3 ); }
                 | '(' TK_BVMUL bitvec_expression_list ')'
		   { $$ = parser_egraph->mkBvmul( $3 ); }
                 | '(' TK_BVNEG bitvec_expression_list ')'
		   { $$ = parser_egraph->mkBvneg( $3 ); }
                 | '(' TK_BVUDIV bitvec_expression_list ')'
		   { $$ = parser_egraph->mkBvudiv( $3 ); }
                 | '(' TK_BVUREM bitvec_expression_list ')'
		   { $$ = parser_egraph->mkBvurem( $3 ); }
                 | '(' TK_BVSDIV bitvec_expression_list ')'
		   { $$ = parser_egraph->mkBvsdiv( $3 ); }
                 | '(' TK_BVSREM bitvec_expression_list ')'
		   { $$ = parser_egraph->mkBvsrem( $3 ); }
                 | '(' TK_SIGN_EXTEND '[' TK_NUM ']' bitvec_expression ')'
		   { $$ = parser_egraph->mkSignExtend( atoi( $4 ), $6 ); free( $4 ); }
                 | '(' TK_ZERO_EXTEND '[' TK_NUM ']' bitvec_expression ')'
		   { $$ = parser_egraph->mkZeroExtend( atoi( $4 ), $6 ); free( $4 ); }
                 | '(' TK_ROTATE_LEFT '[' TK_NUM ']' bitvec_expression ')'
		   { $$ = parser_egraph->mkRotateLeft( atoi( $4 ), $6 ); free( $4 ); }
                 | '(' TK_ROTATE_RIGHT '[' TK_NUM ']' bitvec_expression ')'
		   { $$ = parser_egraph->mkRotateRight( atoi( $4 ), $6 ); free( $4 ); }
                 | '(' TK_BVLSHR bitvec_expression_list ')'
		   { $$ = parser_egraph->mkBvlshr( $3 ); }
                 | '(' TK_BVSHL bitvec_expression_list ')'
		   { $$ = parser_egraph->mkBvshl( $3 ); }
                 | '(' TK_BVASHR bitvec_expression_list ')'
		   { $$ = parser_egraph->mkBvashr( $3 ); }
                 | TK_BVNUM
		   { $$ = parser_egraph->mkBvnum( $1 ); free( $1 ); }
		 | TK_BIT0
		   { $$ = parser_egraph->mkBvnum( const_cast< char * >( "0" ) ); }
		 | TK_BIT1
		   { $$ = parser_egraph->mkBvnum( const_cast< char * >( "1" ) ); }
                 | TK_STR
		   { $$ = parser_egraph->mkVar( $1, true ); free( $1 ); }
	         | TK_LET_STR
	           { $$ = parser_egraph->getDefine( $1 ); free( $1 ); }
	         | '(' TK_ITE formula bitvec_expression bitvec_expression ')'
	           { $$ = parser_egraph->mkIte( $3, $4, $5 ); }
	         | '(' TK_STR expression_list ')'
	           { $$ = parser_egraph->mkUf( $2, $3 ); free( $2 ); }
*/
                 ;

bitvec_expression_list: bitvec_expression bitvec_expression_list
/*
		        { $$ = parser_egraph->cons( $1, $2 ); }
		      | bitvec_expression
			{ $$ = parser_egraph->cons( $1 ); }   
*/
                      ;

array_bitvec_expression_list: bitvec_expression array_element_expression
/*
		              { $$ = parser_egraph->cons( $1, parser_egraph->cons( $2 ) ); }
		            | array_element_expression bitvec_expression
		              { $$ = parser_egraph->cons( $1, parser_egraph->cons( $2 ) ); }   
*/
                            ;

array_expression: '(' TK_ARRAY_STORE array_expression array_index_expression array_element_expression')'
		  { $$ = NULL; }
		/*
   		  { $$ = parser_egraph->mkStore( $3, $4, $5 ); }
                | '(' TK_ARRAY_STORE array_expression bitvec_expression bitvec_expression')'
   		  { $$ = parser_egraph->mkStore( $3, $4, $5 ); }	
	        | '(' TK_ITE formula array_expression array_expression ')'
	           { $$ = parser_egraph->mkIte( $3, $4, $5 ); }
	        | TK_LET_STR
	          { $$ = parser_egraph->getDefine( $1 ); free( $1 ); }
	        | '(' TK_STR expression_list ')'
	          { $$ = parser_egraph->mkUf( $2, $3 ); free( $2 ); }
		| TK_STR
		  { $$ = parser_egraph->mkVar( $1, true ); free( $1 );}
*/
                ;

array_element_expression_list: array_element_expression array_element_expression_list
			     /*
		               { $$ = parser_egraph->cons( $1, $2 ); }
		             | array_element_expression
		               { $$ = parser_egraph->cons( $1 ); }   
                             */
                             ;

array_element_expression: '(' TK_ARRAY_SELECT array_expression array_index_expression ')'
			  { $$ = NULL; }
			/*
			  { $$ = parser_egraph->mkSelect( $3, $4 ); }
                        | '(' TK_ARRAY_SELECT array_expression bitvec_expression ')'
			  { $$ = parser_egraph->mkSelect( $3, $4 ); }	
	        	| '(' TK_ITE formula array_element_expression array_element_expression ')'
	           	  { $$ = parser_egraph->mkIte( $3, $4, $5 ); }
	                | TK_LET_STR
	                  { $$ = parser_egraph->getDefine( $1 ); free( $1 ); }
	        	| '(' TK_STR expression_list ')'
	          	  { $$ = parser_egraph->mkUf( $2, $3 ); free( $2 ); }
			| TK_STR
			  { $$ = parser_egraph->mkVar( $1, true ); free( $1 );}
                        */
			;

array_index_expression: '(' TK_ITE formula array_index_expression array_index_expression ')'
			{ $$ = NULL; }
		      /*
	                { $$ = parser_egraph->mkIte( $3, $4, $5 ); }
	              | TK_LET_STR
	                { $$ = parser_egraph->getDefine( $1 ); free( $1 ); }
	              | '(' TK_STR expression_list ')'
	                { $$ = parser_egraph->mkUf( $2, $3 ); free( $2 ); }
		      | TK_STR
		        { $$ = parser_egraph->mkVar( $1, true ); free( $1 ); }
                      */
		      ;
%%

//=======================================================================================
// Auxiliary Routines

vector< unsigned > * createTypeList( unsigned t )
{
  vector< unsigned > * l = new vector< unsigned >;
  l->push_back( t );
  return l;
} 

vector< unsigned > * createTypeList( unsigned t, const char * size )
{
/*
  assert( t == DTYPE_BITVEC );
*/
  vector< unsigned > * l = new vector< unsigned >;
  const unsigned int_size = atoi( size ); 
  assert( int_size <= MAX_WIDTH );
  l->push_back( t | int_size );
  return l;
} 

vector< unsigned > * pushTypeList( vector< unsigned > * l, unsigned t )
{
  l->push_back( t );
  return l;
}

vector< unsigned > * pushTypeList( vector< unsigned > * l, unsigned t, const char * size )
{
  const unsigned int_size = atoi( size );
  assert( int_size <= MAX_WIDTH );
  l->push_back( t | int_size );
  return l;
}

void destroyTypeList( vector< unsigned > * l )
{
  delete l;
}
