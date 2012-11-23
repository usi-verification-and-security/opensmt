/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2010, Roberto Bruttomesso

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
#include "cnfparser.h"

%}

%option noyywrap
%option yylineno
%option nounput

%%

[ \t\n]                  { }
^"c".*\n                 { }
^"0"                     { }
"p"                      { return TK_P; }
"cnf"                    { return TK_CNF; }
"-"                      { return TK_NOT; }
"0"                      { return TK_END; }
[1-9][0-9]*              { cnflval.str = strdup( yytext ); return TK_NUM; }
"%"                      { } 
.                        { printf( "Syntax error at line %d near %s\n", yylineno, yytext ); exit( 1 ); }

%%
