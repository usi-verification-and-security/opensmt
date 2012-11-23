/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

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

#include <cstdio>
#include <cstdlib>
/* Keep the following headers in their original order */
#include "Egraph.h"
#include "smtparser.h"

#define BUFFER_LENGTH 1024

char   buffer[ BUFFER_LENGTH ];
char * pbuffer;
  
%}

%x start_source
%x start_comment
%option noyywrap
%option yylineno
%option nounput

%%

[ \t\n]                  { }
";".*\n                  { }
"benchmark"              { return TK_BENCHMARK; }
":extrasorts"            { return TK_EXTRASORTS; }
":extrapreds"            { return TK_EXTRAPREDS; }
":extrafuns"             { return TK_EXTRAFUNS; }
":assumption"            { return TK_ASSUMPTION; }
":formula"               { return TK_FORMULA; }
":interpolate"           { return TK_INTERPOLATE; }
":source"                { return TK_SOURCE; }
":logic"                 { return TK_LOGIC; }
":status"                { return TK_STATUS; }
":category"              { return TK_CATEGORY; }
":difficulty"            { return TK_DIFFICULTY; }
":notes"                 { return TK_NOTES; }
"U"                      { return TK_U; }    
"Real"			 { return TK_REAL; }
"Int"                    { return TK_INT; }
"BitVec"                 { return TK_BITVEC; }   
"Array"		 	 { return TK_ARRAY; } 
"Index"		 	 { return TK_ARRAY_INDEX; }
"Element"		 { return TK_ARRAY_ELEMENT; }
"repeat"                 { return TK_REPEAT; }
"+"                      { return TK_PLUS; }
"-"                      { return TK_MINUS; }
"~"                      { return TK_UMINUS; }
"*"                      { return TK_TIMES; }
"/"                      { return TK_DIV; }
"="                      { return TK_EQ; }
"<="                     { return TK_LEQ; }
">="                     { return TK_GEQ; }
"<"                      { return TK_LT; }
">"                      { return TK_GT; }
"bvslt"                  { return TK_BVSLT; }
"bvsgt"                  { return TK_BVSGT; }
"bvsle"                  { return TK_BVSLE; }
"bvsge"                  { return TK_BVSGE; }
"bvult"                  { return TK_BVULT; }
"bvugt"                  { return TK_BVUGT; }
"bvule"                  { return TK_BVULE; }
"bvuge"                  { return TK_BVUGE; }
"concat"                 { return TK_CONCAT; }
"extract"                { return TK_EXTRACT; }
"bvand"                  { return TK_BVAND; }
"bvor"                   { return TK_BVOR; }
"bvxor"                  { return TK_BVXOR; }
"bvnot"                  { return TK_BVNOT; }
"bvadd"                  { return TK_BVADD; }
"bvsub"                  { return TK_BVSUB; }
"bvmul"                  { return TK_BVMUL; }
"bvneg"                  { return TK_BVNEG; }
"bvlshr"                 { return TK_BVLSHR; }
"bvashr"                 { return TK_BVASHR; }
"bvshl"                  { return TK_BVSHL; }
"bvsrem"                 { return TK_BVSREM; }
"bvurem"                 { return TK_BVUREM; }
"bvsdiv"                 { return TK_BVSDIV; }
"bvudiv"                 { return TK_BVUDIV; }
"select"		 { return TK_ARRAY_SELECT; }
"store"			 { return TK_ARRAY_STORE; }
"sign_extend"            { return TK_SIGN_EXTEND; }
"zero_extend"            { return TK_ZERO_EXTEND; }
"rotate_left"            { return TK_ROTATE_LEFT; }
"rotate_right"           { return TK_ROTATE_RIGHT; }
"implies"                { return TK_IMPLIES; }
"and"			 { return TK_AND; }
"or"			 { return TK_OR; }
"not"			 { return TK_NOT; }
"iff"                    { return TK_IFF; }
"xor"                    { return TK_XOR; }
"flet"                   { return TK_FLET; }
"let"                    { return TK_LET; }
"true"                   { return TK_TRUE; }
"false"                  { return TK_FALSE; }
"ite"                    { return TK_ITE; }
"if_then_else"           { return TK_IFTHENELSE; }
"distinct"               { return TK_DISTINCT; }
"bit0"                   { return TK_BIT0; }
"bit1"                   { return TK_BIT1; }

[0-9]+                   { smtlval.str = strdup( yytext ); return TK_NUM; }
bv[0-9]+                 { smtlval.str = strdup( yytext ); return TK_BVNUM_NO_WIDTH; }
bv[0-9]+\[[0-9]+\]       { smtlval.str = strdup( yytext ); return TK_BVNUM; }
bvbin[0-1]+              { smtlval.str = strdup( yytext ); return TK_BVNUM; }
[_a-zA-Z0-9\.\']+        { smtlval.str = strdup( yytext ); return TK_STR; }
[\$_a-zA-Z0-9\.]+        { smtlval.str = strdup( yytext ); return TK_FLET_STR; }
[\?_a-zA-Z0-9\.]+        { smtlval.str = strdup( yytext ); return TK_LET_STR; }

\"[_a-zA-Z0-9\.\' \t]+\" { smtlval.str = strdup( yytext ); return TK_ARGUMENT; }

[\{]          { pbuffer = buffer; BEGIN(start_source); }

<start_source>{
  \\\}          { *pbuffer++ = '}'; }
  [^\}\n]       { *pbuffer++ = yytext[0]; }
  \n            { *pbuffer++ = '\n'; }
  [\}\"]        { *pbuffer = '\0'; smtlval.str = strdup( buffer );
                   BEGIN(INITIAL); return TK_ARGUMENT; }
}

[()\{\}\[\]\:]           { return *yytext; }
.                        { printf( "Syntax error at line %d near %s\n", yylineno, yytext ); exit( 1 ); }

%%
