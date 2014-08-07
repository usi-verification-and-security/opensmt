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

#include <cstdio>
#include <cstdlib>
/* Keep the following headers in their original order */
#include "Egraph.h"
#include "ParserTypes.h"
#include "smt2parser.h"


#define BUFFER2_LENGTH 1024
char   buffer2[ BUFFER2_LENGTH ];
char * pbuffer2;

  
%}

%x start_source
%x start_comment
%option noyywrap
%option yylineno
%option nounput

%%

[ \t\n]                      { }
";".*\n                      { }
":print-success"             { return TK_PRINT_SUCCESS; }
":expand-definitions"        { return TK_EXPAND_DEFINITIONS; }
":interactive-mode"          { return TK_INTERACTIVE_MODE; }
":produce-proofs"            { return TK_PRODUCE_PROOFS; }
":produce-unsat-cores"       { return TK_PRODUCE_UNSAT_CORES; }
":produce-interpolants"      { return TK_PRODUCE_INTERPOLANTS; }
":produce-models"            { return TK_PRODUCE_MODELS; }
":produce-assignments"       { return TK_PRODUCE_ASSIGNMENTS; }
":regular-output-channel"    { return TK_REGULAR_OUTPUT_CHANNEL; }
":diagnostic-output-channel" { return TK_DIAGNOSTIC_OUTPUT_CHANNEL; }
":random-seed"               { return TK_RANDOM_SEED; }
":verbosity"                 { return TK_VERBOSITY; }
"set-logic"                  { return TK_SETLOGIC; }
"set-info"                   { return TK_SETINFO; }
"set-option"                 { return TK_SETOPTION; }
"declare-sort"               { return TK_DECLARESORT; }
"define-sort"                { return TK_DEFINESORT; }
"declare-fun"                { return TK_DECLAREFUN; }
"define-fun"                 { return TK_DEFINEFUN; }
"push"                       { return TK_PUSH; }
"pop"                        { return TK_POP; }
"check-sat"                  { return TK_CHECKSAT; }
"get-assertions"             { return TK_GETASSERTIONS; }
"get-proof"                  { return TK_GETPROOF; }
"get-interpolants"           { return TK_GETINTERPOLANTS; }
"get-unsat-core"             { return TK_GETUNSATCORE; }
"get-value"                  { return TK_GETVALUE; }
"get-assignment"             { return TK_GETASSIGNMENT; }
"get-option"                 { return TK_GETOPTION; }
"get-info"                   { return TK_GETINFO; }
"exit"                       { return TK_EXIT; }
"as"                         { return TK_AS; }
"distinct"                   { return TK_DISTINCT; }
"let"                        { return TK_LET; }
"forall"                     { return TK_FORALL; }
"exists"                     { return TK_EXISTS; }
"!"                          { return TK_ANNOT; }
"assert"                     { return TK_ASSERT; }
"+"                          { return TK_PLUS; }
"-"                          { return TK_MINUS; }
"*"                          { return TK_TIMES; }
"/"                          { return TK_DIV; }
"="                          { return TK_EQ; }
"<="                         { return TK_LEQ; }
">="                         { return TK_GEQ; }
"<"                          { return TK_LT; }
">"                          { return TK_GT; }
"bvslt"                      { return TK_BVSLT; }
"bvsgt"                      { return TK_BVSGT; }
"bvsle"                      { return TK_BVSLE; }
"bvsge"                      { return TK_BVSGE; }
"bvult"                      { return TK_BVULT; }
"bvugt"                      { return TK_BVUGT; }
"bvule"                      { return TK_BVULE; }
"bvuge"                      { return TK_BVUGE; }
"concat"                     { return TK_CONCAT; }
"extract"                    { return TK_EXTRACT; }
"bvand"                      { return TK_BVAND; }
"bvor"                       { return TK_BVOR; }
"bvxor"                      { return TK_BVXOR; }
"bvnot"                      { return TK_BVNOT; }
"bvadd"                      { return TK_BVADD; }
"bvsub"                      { return TK_BVSUB; }
"bvmul"                      { return TK_BVMUL; }
"bvneg"                      { return TK_BVNEG; }
"bvlshr"                     { return TK_BVLSHR; }
"bvashr"                     { return TK_BVASHR; }
"bvshl"                      { return TK_BVSHL; }
"bvsrem"                     { return TK_BVSREM; }
"bvurem"                     { return TK_BVUREM; }
"bvsdiv"                     { return TK_BVSDIV; }
"store"                      { return TK_STORE; }
"select"                     { return TK_SELECT; }
"diff"                       { return TK_DIFF; }
"sign_extend"                { return TK_SIGN_EXTEND; }
"zero_extend"                { return TK_ZERO_EXTEND; }
"rotate_left"                { return TK_ROTATE_LEFT; }
"rotate_right"               { return TK_ROTATE_RIGHT; }
"=>"                         { return TK_IMPLIES; }
"and"			     { return TK_AND; }
"or"			     { return TK_OR; }
"not"			     { return TK_NOT; }
"iff"                        { return TK_IFF; }
"xor"                        { return TK_XOR; }
"true"                       { return TK_TRUE; }
"false"                      { return TK_FALSE; }
"ite"                        { return TK_ITE; }
"Array"		             { return TK_ARRAY; }
"Int"                        { return TK_INT; }
"Real"                       { return TK_REAL; }
"Bool"                       { return TK_BOOL; }

0|[1-9][0-9]*                                                                  { smt2lval.str = strdup( yytext ); return TK_NUM; }
[0-9]+\.0*[0-9]+                                                               { smt2lval.str = strdup( yytext ); return TK_DEC; }
#x[a-fA-F0-9]+                                                                 { smt2lval.str = strdup( yytext ); return TK_HEX; }
#b[0-1]+                                                                       { smt2lval.str = strdup( yytext ); return TK_BIN; }
\:[a-zA-Z0-9~!@\$\%\^&\*_\-\+=\<\>\.\?\/]+                                     { smt2lval.str = strdup( yytext ); return TK_KEY; }
[a-zA-Z~!@\$\%\^&\*\-\+=\<\>\.\?\/'][a-zA-Z0-9~!@\$\%\^&\*_\-\+=\<\>\.\?\/']*|_[a-zA-Z0-9~!@\$\%\^&\*_\-\+=\<\>\.\?\/']+ { smt2lval.str = strdup( yytext ); return TK_SYM; }



\|		{ pbuffer2 = buffer2; BEGIN(start_source); }
<start_source>{
  [^\|\n]       { *pbuffer2++ = yytext[0]; }
  \n            { *pbuffer2++ = '\n'; }
  \|            { *pbuffer2 = '\0'; smt2lval.str = strdup( buffer2 );
                   BEGIN(INITIAL); return TK_SYM; }
}

\".*\"          { smt2lval.str = strdup( yytext ); return TK_STR; }    
[()]            { return *yytext; }
_               { return *yytext; }
.               { printf( "Syntax error at line %d near %s\n", yylineno, yytext ); exit( 1 ); }

%%
