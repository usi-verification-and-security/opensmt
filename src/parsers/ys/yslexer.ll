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
