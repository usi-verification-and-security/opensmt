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
#include "ysparser.h"

%}

%option noyywrap
%option yylineno
%option nounput

%%

[ \t\n]                  { }
";;".*\n                 { }
"set-evidence!"          { return TK_EVIDENCE; }
"reset"                  { return TK_RESET; }
"define"		 { return TK_DEFINE; }
"subrange"               { return TK_SUBRANGE; }
"assert"		 { return TK_ASSERT; }
"assert+"		 { return TK_EXTASSERT; }
"check"  		 { return TK_CHECK; }
"::"		         { return TK_SEPARATOR; }
"int"                    { return TK_INT; }
"bool"                   { return TK_BOOL; }
"<"                      { return TK_LT; }
"<="                     { return TK_LEQ; }
"+"                      { return TK_PLUS; }
"-"                      { return TK_MINUS; }
"=>"                     { return TK_IMPLIES; }
"/="                     { return TK_NEQ; }
"="                      { return TK_EQ; }
"if"                     { return TK_IF; }
"and"			 { return TK_AND; }
"or"			 { return TK_OR; }
"not"			 { return TK_NOT; }
"true"                   { return TK_TRUE; }
"false"                  { return TK_FALSE; }

[0-9]+                   { yslval.str = strdup( yytext ); return TK_NUM; }
[_a-zA-Z0-9\.\@]+        { yslval.str = strdup( yytext ); return TK_STR; }

[()\{\}\[\]\:]           { return *yytext; }
.                        { printf( "Syntax error at line %d near %s\n", yylineno, yytext ); exit( 1 ); }

%%
