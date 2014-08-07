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
#include "SStore.h"
#include "ParserTypes.h"
#include "OpenSMTContext.h"
#include <cstdio>
#include <cstdlib>
#include <cassert>

extern int smt2lineno;
extern int smt2lex( );
extern OpenSMTContext * parser_ctx;

vector< string > * createNumeralList  ( const char * );
vector< string > * pushNumeralList    ( vector< string > *, const char * );
void		   destroyNumeralList ( vector< string > * );

list< Snode * > * createSortList  ( Snode * );
list< Snode * > * pushSortList    ( list< Snode * > *, Snode * );
void		  destroySortList ( list< Snode * > * );

list< Anode * > * createAttrList  ( Anode * );
list< Anode * > * pushAttrList    ( list< Anode * > *, Anode * );
void		  destroyAttrList ( list< Anode * > * );

class             SpNode;


void smt2error( const char * s )
{
  printf( "At line %d: %s\n", smt2lineno, s );
  exit( 1 );
}

/* Overallocation to prevent stack overflow */
#define YYMAXDEPTH 1024 * 1024
%}

%union
{
  char  *                   str;
  vector< string > *        str_list;
  Enode *                   enode;
  Snode *                   snode;
  list< Snode * > *         snode_list;
  map< Enode *, Enode * > * binding_list;
  Anode *                   anode;
  list< Anode * > *         anode_list;
  SpNode *                  spnode;
  IdNode *                  idnode;
}

%error-verbose

%token TK_NUM TK_DEC TK_HEX TK_STR TK_SYM TK_KEY TK_BIN
%token TK_BOOL
%token TK_SETLOGIC TK_SETINFO TK_SETOPTION TK_DECLARESORT TK_DEFINESORT TK_DECLAREFUN
%token TK_PUSH TK_POP TK_CHECKSAT TK_GETASSERTIONS TK_GETPROOF TK_GETUNSATCORE TK_GETINTERPOLANTS
%token TK_GETVALUE TK_GETASSIGNMENT TK_GETOPTION TK_GETINFO TK_EXIT
%token TK_AS TK_LET TK_FORALL TK_EXISTS TK_ANNOT TK_DISTINCT TK_DEFINEFUN
%token TK_ASSERT 
%token TK_REAL TK_INT TK_ARRAY
%token TK_PLUS TK_MINUS TK_TIMES TK_UMINUS TK_DIV
%token TK_NE TK_EQ TK_LEQ TK_GEQ TK_LT TK_GT
%token TK_AND TK_OR TK_NOT TK_IFF TK_XOR TK_ITE TK_IFTHENELSE TK_IMPLIES
%token TK_TRUE TK_FALSE TK_INTERPOLATE
%token TK_BVSLT TK_BVSGT TK_BVSLE TK_BVSGE
%token TK_BVULT TK_BVUGT TK_BVULE TK_BVUGE
%token TK_EXTRACT TK_CONCAT TK_BVAND TK_BVOR TK_BVXOR TK_BVNOT TK_BVADD TK_BVNEG TK_BVMUL TK_BVASHR TK_REPEAT
%token TK_SIGN_EXTEND TK_ZERO_EXTEND TK_ROTATE_LEFT TK_ROTATE_RIGHT TK_BVLSHR TK_BVSHL TK_BVSREM TK_BVSDIV TK_BVSUB
%token TK_BVUDIV TK_BVUREM
%token TK_PRINT_SUCCESS TK_EXPAND_DEFINITIONS TK_INTERACTIVE_MODE TK_PRODUCE_PROOFS TK_PRODUCE_UNSAT_CORES TK_PRODUCE_INTERPOLANTS
%token TK_PRODUCE_MODELS TK_PRODUCE_ASSIGNMENTS TK_REGULAR_OUTPUT_CHANNEL TK_DIAGNOSTIC_OUTPUT_CHANNEL
%token TK_RANDOM_SEED TK_VERBOSITY
%token TK_STORE TK_SELECT TK_DIFF

%type <str> TK_NUM TK_DEC TK_HEX TK_BIN TK_STR TK_SYM TK_KEY numeral decimal hexadecimal binary symbol
%type <str> b_value
%type <idnode> identifier
%type <spnode> spec_const
%type <anode> s_expr
%type <anode_list> attribute_value
%type <anode> attribute
%type <anode_list> s_expr_list
%type <str_list> numeral_list
%type <enode> term_list term
%type <snode> sort
%type <snode_list> sort_list
%start script

%%

script: command_list

command_list: command_list command | command ;

command: '(' TK_SETLOGIC symbol ')'
         { parser_ctx->SetLogic( $3 ); free( $3 ); }
       | '(' TK_SETOPTION option ')'
         { }
       | '(' TK_SETINFO attribute ')'
         { parser_ctx->SetInfo( $3 ); free( $3 ); }
       | '(' TK_DECLARESORT symbol numeral ')'
	 { parser_ctx->DeclareSort( $3, atoi($4) ); free( $3 ); free( $4 ); }
       /*
       | '(' TK_DEFINESORT symbol '(' symbol_list ')' sort ')'
	 { opensmt_error2( "define-sort is not supported (yet)", "" ); }
       */
       | '(' TK_DECLAREFUN symbol '(' sort_list ')' sort ')'
	 { 
	   Snode * a = parser_ctx->mkCons( *$5 );
	   Snode * s = parser_ctx->mkSort( a );
	   parser_ctx->DeclareFun( $3, s, $7 );
	   destroySortList( $5 ); free( $3 );
	 }
       | '(' TK_DECLAREFUN symbol '(' ')' sort ')'
	 { parser_ctx->DeclareFun( $3, NULL, $6 ); free( $3 ); }
       /*
       | '(' TK_DEFINEFUN symbol '(' sorted_var_list ')' sort term ')'
	 { opensmt_error2( "command not supported (yet)", "" ); }
       | '(' TK_DEFINEFUN symbol '(' ')' sort ')'
	 { opensmt_error2( "command not supported (yet)", "" ); }
       */
       | '(' TK_PUSH numeral ')'
	 { parser_ctx->addPush( atoi( $3 ) ); free( $3 ); }
       | '(' TK_POP numeral ')'
	 { parser_ctx->addPop( atoi( $3 ) ); free( $3 );}
       | '(' TK_ASSERT term ')'
         { parser_ctx->addAssert( $3 ); }
       | '(' TK_CHECKSAT ')'
	 { parser_ctx->addCheckSAT( ); }
       /*
       | '(' TK_GETASSERTIONS ')'
	 { opensmt_error2( "command not supported (yet)", "" ); }
       */
       | '(' TK_GETPROOF ')'
	 { parser_ctx->addGetProof( ); }
       | '(' TK_GETINTERPOLANTS ')'
	 { parser_ctx->addGetInterpolants( ); }
       /*
       | '(' TK_GETUNSATCORE ')'
	 { opensmt_error2( "command not supported (yet)", "" ); }
       | '(' TK_GETVALUE '(' term_list ')' ')'
	 { opensmt_error2( "command not supported (yet)", "" ); }
       | '(' TK_GETASSIGNMENT ')'
	 { opensmt_error2( "command not supported (yet)", "" ); }
       | '(' TK_GETOPTION keyword ')'
	 { opensmt_error2( "command not supported (yet)", "" ); }
       */
     /*| '(' TK_GETINFO info_flag ')'*/
       | '(' TK_EXIT ')'
         { parser_ctx->addExit( ); }
       ;

s_expr: spec_const
        { $$ = new Anode( $1->type, $1->value, NULL ); }
      | TK_SYM
        { $$ = new Anode( AT_SYM, $1, NULL ); }
      | TK_KEY 
        { $$ = new Anode( AT_KEY, $1, NULL ); }
      /*
      | '(' s_expr ')' 
      */
      ;

spec_const: numeral
	    { $$ = new SpNode( AT_NUM, $1 ); }
	  | decimal
	    { $$ = new SpNode( AT_DEC, $1 ); }
	  | hexadecimal
	    { $$ = new SpNode( AT_DEC, $1 ); }
	  | binary
	    { $$ = new SpNode( AT_BIN, $1 ); }
	  | TK_STR
	    { $$ = new SpNode( AT_STR, $1 ); }
          ;

identifier: TK_SYM
	    { $$ = new IdNode($1, NULL); }
	  | '(' '_' TK_SYM numeral_list ')' { $$ = new IdNode($3, $4); }
	  ;

keyword: TK_KEY { free($1); };

symbol: TK_SYM 
        { $$ = $1; }
      ;

symbol_list: symbol_list symbol | symbol ;

attribute: TK_KEY
        {
            $$ = new Anode(AT_KEY, $1, NULL);
        }
        | TK_KEY attribute_value
        {
            $$ = new Anode(AT_KEY, $1, $2);
        }
        ;

attribute_value: spec_const
        {
            Anode* a = new Anode( $1->type, $1->value, NULL );
            $$ = createAttrList( a );
        }
        | TK_SYM
        {
            Anode* a = new Anode( AT_SYM, $1, NULL );
            $$ = createAttrList( a );
        }
        | '(' s_expr_list ')'
        {
            Anode* a = new Anode( AT_NONE, NULL, $2 );
            $$ = createAttrList( a );
        }
        | '(' ')'
        {
            Anode* a = new Anode( AT_NONE, NULL, NULL );
            $$ = createAttrList( a );
        }
        ;

sort: TK_BOOL 
      { $$ = parser_ctx->mkSortBool( ); }
    | TK_INT
      { $$ = parser_ctx->mkSortInt( ); }
    | TK_REAL
      { $$ = parser_ctx->mkSortReal( ); }
    | '(' TK_ARRAY sort sort ')'
      {
        IdNode* idNode = new IdNode( "Array", NULL );
        Snode * a = parser_ctx->mkSortVar( idNode );
        $$ = parser_ctx->mkSort(
                 parser_ctx->mkCons( a
               , parser_ctx->mkCons( $3
               , parser_ctx->mkCons( $4 ) ) ) );
      }
    | identifier 
      { $$ = parser_ctx->mkSortVar( $1 ); free( $1 ); }
    | '(' identifier sort_list ')' 
      { 
        Snode * s = parser_ctx->mkCons( parser_ctx->mkSortVar( $2 ) ); 
	(*$3).push_front( s );
	$$ = parser_ctx->mkSort( parser_ctx->mkCons( *$3 ) );
        free( $2 ); 
      }
    ;

sorted_var: '(' TK_SYM sort ')' ;

term: spec_const 
      { $$ = parser_ctx->mkNum( $1->value ); free( $1 ); }
  /* 
   * List of predefined identifiers 
   */
    | TK_TRUE
      { $$ = parser_ctx->mkTrue( ); }
    | TK_FALSE
      { $$ = parser_ctx->mkFalse( ); }
    | '(' TK_AND term_list ')'
      { $$ = parser_ctx->mkAnd( $3 ); }
    | '(' TK_OR term_list ')'
      { $$ = parser_ctx->mkOr( $3 ); }
    | '(' TK_XOR term_list ')'
      { $$ = parser_ctx->mkXor( $3 ); }
    | '(' TK_NOT term_list ')'
      { $$ = parser_ctx->mkNot( $3 ); }
    | '(' TK_IMPLIES term_list ')'
      { $$ = parser_ctx->mkImplies( $3 ); }
    | '(' TK_EQ term_list ')'
      { $$ = parser_ctx->mkEq( $3 ); }
    | '(' TK_ITE term_list ')'
      { $$ = parser_ctx->mkIte( $3 ); }
    | '(' TK_PLUS term_list ')'
      { $$ = parser_ctx->mkPlus( $3 ); }
    | '(' TK_MINUS term_list ')'
      { $$ = parser_ctx->mkMinus( $3 ); }
    | '(' TK_TIMES term_list ')'
      { $$ = parser_ctx->mkTimes( $3 ); }
    | '(' TK_UMINUS term_list ')'
      { $$ = parser_ctx->mkUminus( $3 ); }
    | '(' TK_DIV term_list ')'
      { $$ = parser_ctx->mkDiv( $3 ); }
    | '(' TK_LEQ term_list ')'
      { $$ = parser_ctx->mkLeq( $3 ); }
    | '(' TK_GEQ term_list ')'
      { $$ = parser_ctx->mkGeq( $3 ); }
    | '(' TK_LT term_list ')'
      { $$ = parser_ctx->mkLt( $3 ); }
    | '(' TK_GT term_list ')'
      { $$ = parser_ctx->mkGt( $3 ); }
    | '(' TK_DISTINCT term_list ')'
      { $$ = parser_ctx->mkDistinct( $3 ); }
    | '(' TK_STORE term term term ')'
      { $$ = parser_ctx->mkStore( $3, $4, $5 ); }
    | '(' TK_SELECT term term ')'
      { $$ = parser_ctx->mkSelect( $3, $4 ); }
    | '(' TK_DIFF term term ')'
      { $$ = parser_ctx->mkDiff( $3, $4 ); }
    | '(' TK_LET '(' var_binding_list ')' term ')'
      { $$ = $6; }
    /*
    | '(' TK_FORALL '(' sorted_var_list ')' term ')'
      { opensmt_error2( "case not handled (yet)", "" ); }
    | '(' TK_EXISTS '(' sorted_var_list ')' term ')'
      { opensmt_error2( "case not handled (yet)", "" ); }
    | '(' TK_ANNOT term attribute_list ')'
      { opensmt_error2( "case not handled (yet)", "" ); }
    */
  /*
   * Variable
   */
    | identifier 
      { $$ = parser_ctx->mkVar( $1->name ); free( $1 ); }
  /*
   * Function application
   */
    | '(' identifier term_list ')'
      { $$ = parser_ctx->mkFun( $2->name, $3 ); free( $2 ); }
    /*
    | '(' TK_AS identifier sort ')' 
      { opensmt_error2( "case not handled (yet)", "" ); }
    */
    ;

sort_list: sort_list sort 
	   { $$ = pushSortList( $1, $2 ); }
	 | sort 
	   { $$ = createSortList( $1 ); }
         ;

sorted_var_list: sorted_var_list sorted_var | sorted_var ;

var_binding_list: var_binding_list '(' TK_SYM term ')'
		  { parser_ctx->mkBind( $3, $4 ); free($3); }
                | '(' TK_SYM term ')'
		  { parser_ctx->mkBind( $2, $3 ); free($2); }
		;

term_list: term term_list
	   { $$ = parser_ctx->mkCons( $1, $2 ); }
	 | term 
           { $$ = parser_ctx->mkCons( $1 ); }
         ;

s_expr_list: s_expr_list s_expr
         { $$ = pushAttrList( $1, $2 ); }
         | s_expr
         { $$ = createAttrList( $1 ); }
         ;

numeral_list: numeral_list numeral
	      { $$ = pushNumeralList( $1, $2 ); }
	    | numeral
	      { $$ = createNumeralList( $1 ); }
	    ;

numeral: TK_NUM { $$ = $1; } ;

decimal: TK_DEC { $$ = $1; } ;

hexadecimal: TK_HEX { $$ = $1; } ;

binary: TK_BIN { $$ = $1; };

option: TK_PRINT_SUCCESS b_value
        { 
	  parser_ctx->SetOption( ":print-success", $2 );
	  free( $2 );
        }
      | TK_EXPAND_DEFINITIONS b_value
	{
	  parser_ctx->SetOption( ":expand-definitions", $2 );
          free( $2 );
        }
      | TK_INTERACTIVE_MODE b_value
	{
	  parser_ctx->SetOption( ":interactive-mode", $2 );
          free( $2 );
        }
      | TK_PRODUCE_PROOFS b_value
	{
	  parser_ctx->SetOption( ":produce-proofs", $2 );
          free( $2 );
        }
      | TK_PRODUCE_UNSAT_CORES b_value
	{
	  parser_ctx->SetOption( ":produce-unsat-cores", $2 );
          free( $2 );
        }
      | TK_PRODUCE_INTERPOLANTS b_value
	{
	  parser_ctx->SetOption( ":produce-interpolants", $2 );
          free( $2 );
        }
      | TK_PRODUCE_MODELS b_value
	{
	  parser_ctx->SetOption( ":produce-models", $2 );
          free( $2 );
        }
      | TK_PRODUCE_ASSIGNMENTS b_value
	{
	  parser_ctx->SetOption( ":produce-assignments", $2 );
          free( $2 );
        }
      | TK_REGULAR_OUTPUT_CHANNEL TK_STR
	{
	  char buf[256] = ":regular-output-channel "; 
	  strcat( buf, $2 );
	  parser_ctx->SetOption( ":regular-output-channel", $2 );
          free( $2 );
        }
      | TK_DIAGNOSTIC_OUTPUT_CHANNEL TK_STR
	{
	  parser_ctx->SetOption( ":diagnostic-output-channel", $2 );
          free( $2 );
        }
      | TK_RANDOM_SEED TK_NUM
	{
	  parser_ctx->SetOption( ":random-seed", $2 );
          free( $2 );
        }
      | TK_VERBOSITY TK_NUM
	{
	  parser_ctx->SetOption( ":verbosity", $2 );
          free( $2 );
	}
      | TK_KEY
	{ parser_ctx->SetOption( $1 ); free( $1 ); }
      | TK_KEY s_expr
	{ 
	  parser_ctx->SetOption( $1, $2->value ); 
	  free( $1 ); free( $2 ); 
        }
      ;
      
b_value: TK_TRUE
         { 
           char * buf;
           buf = (char *)malloc(sizeof(char) * 10);
	   strcpy( buf, "true" );
	   $$ = buf;
         }
       | TK_FALSE
         {
           char * buf;
           buf = (char *)malloc(sizeof(char) * 10);
	   strcpy( buf, "false" );
	   $$ = buf;
	 }
       ;

%%

//=======================================================================================
// Auxiliary Routines

vector< string > * createNumeralList( const char * s )
{
  vector< string > * l = new vector< string >;
  l->push_back( s );
  return l;
} 

vector< string > * pushNumeralList( vector< string > * l, const char * s )
{
  l->push_back( s );
  return l;
}

void destroyNumeralList( vector< string > * l )
{
  delete l;
}

list< Snode * > * createSortList( Snode * s )
{
  list< Snode * > * l = new list< Snode * >;
  l->push_back( s );
  return l;
} 

list< Snode * > * pushSortList( list< Snode * > * l, Snode * s )
{
  l->push_back( s );
  return l;
}

void destroySortList( list< Snode * > * l )
{
  assert( l );
  delete l;
}

list< Anode * > * createAttrList( Anode * a )
{
  list< Anode * > * l = new list< Anode * >;
  l->push_back( a );
  return l;
} 

list< Anode * > * pushAttrList( list< Anode * > * l, Anode * a )
{
  l->push_back( a );
  return l;
}

void destroyAttrList( list< Anode * > * l )
{
  assert( l );
  delete l;
}
