/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT -- Copyright (C) 2012 - 2014 Antti Hyvarinen

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


%option prefix="smt2new"
%option reentrant
%option bison-bridge
%option bison-locations
%option noyywrap
%option yylineno
%option stack

%{

#include <cstdio>
#include <cstdlib>
#include <vector>
#include <list>

#include "smt2newcontext.h"
#include "smt2newparser.h"

#define YY_EXTRA_TYPE Smt2newContext*
#define YY_USER_ACTION yyget_lloc(yyscanner)->first_line = yyget_lineno(yyscanner);
%}

%x STR
%x PSYM

%%

\;.*                         // Eat comments
[ \t\n]+                     // Eat spaces

"!"        { return *yyget_text(yyscanner);                                                   }
"_"        { return *yyget_text(yyscanner);                                                   }
"as"       { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_AS;      }
"DECIMAL"  { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_DECIMAL; }
"exists"   { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_EXISTS;  }
"forall"   { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_FORALL;  }
"let"      { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_LET;     }
"NUMERAL"  { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_NUMERAL; }
"par"      { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_PAR;     }
"STRING"   { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_STRING;  }

"assert"          { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_ASSERT;        }
"check-sat"       { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_CHECKSAT;      }
"declare-sort"    { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_DECLARESORT;   }
"declare-fun"     { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_DECLAREFUN;    }
"define-sort"     { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_DEFINESORT;    }
"define-fun"      { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_DEFINEFUN;     }
"exit"            { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_EXIT;          }
"get-assertions"  { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_GETASSERTIONS; }
"get-assignment"  { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_GETASSIGNMENT; }
"get-info"        { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_GETINFO;       }
"get-option"      { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_GETOPTION;     }
"get-proof"       { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_GETPROOF;      }
"get-unsat-core"  { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_GETUNSATCORE;  }
"get-value"       { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_GETVALUE;      }
"pop"             { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_POP;           }
"push"            { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_PUSH;          }
"set-logic"       { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_SETLOGIC;      }
"set-info"        { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_SETINFO;       }
"set-option"      { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_SETOPTION;     }
"get-interpolants" { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_GETITPS;      }
"theory"          { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_THEORY;        }

":sorts"                     { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_SORTS;                   }
":funs"                      { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_FUNS;                    }
":sorts-description"         { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_SORTSDESCRIPTION;        }
":funs-description"          { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_FUNSDESCRIPTION;         }
":definition"                { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_DEFINITION;              }
":values"                    { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_VALUES;                  }
":notes"                     { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_NOTES;                   }
":theories"                  { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_THEORIES;                }
":language"                  { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_LANGUAGE;                }
":extensions"                { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_EXTENSIONS;              }
":print-success"             { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_PRINTSUCCESS;            }
":expand-definitions"        { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_EXPANDDEFINITIONS;       }
":interactive-mode"          { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_INTERACTIVEMODE;         }
":produce-proofs"            { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_PRODUCEPROOFS;           }
":produce-unsat-cores"       { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_PRODUCEUNSATCORES;       }
":produce-models"            { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_PRODUCEMODELS;           }
":produce-assignments"       { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_PRODUCEASSIGNMENTS;      }
":regular-output-channel"    { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_REGULAROUTPUTCHANNEL;    }
":diagnostic-output-channel" { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_DIAGNOSTICOUTPUTCHANNEL; }
":random-seed"               { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_RANDOMSEED;              }
":verbosity"                 { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_VERBOSITY;               }
":error-behavior"            { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_ERRORBEHAVIOR;           }
":name"                      { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_NAME;                    }
":named"                     { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_NAMED;                   }
":authors"                   { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_AUTHORS;                 }
":version"                   { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_VERSION;                 }
":status"                    { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_STATUS;                  }
":reason-unknown"            { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_REASONUNKNOWN;           }
":all-statistics"            { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return KW_ALLSTATISTICS;           }


0|[1-9][0-9]*                { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_NUM; }
[0-9]+\.0*[0-9]+             { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_DEC; }
#x[0-9a-fA-F]+               { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_HEX; }
#b[01]+                      { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_BIN; }

[a-zA-Z~!@\$\%\^&\*\-\+=\<\>\.\?\/'_][a-zA-Z0-9~!@\$\%\^&\*_\-\+=\<\>\.\?\/']* { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_SYM; }
\:[a-zA-Z0-9~!@\$\%\^&\*_\-\+=\<\>\.\?\/]+ { yyget_lval(yyscanner)->str = strdup( yyget_text(yyscanner) ); return TK_KEY; }

[()]            { return *yyget_text(yyscanner); }

\"              { yy_push_state(STR, yyscanner); }

<STR>{
  [ ]           { yyextra->insertBuf(' ');                                       }
  [\t]          { yyextra->insertBuf('\t');                                      }
  \n            { yyextra->insertBuf('\n');                                      }
  \\\"          { yyextra->insertBuf('"');                                       }
  \\\\          { yyextra->insertBuf('\\');                                      }
  [^\\\n\"]     { yyextra->insertBuf(yyget_text(yyscanner)[0]);                  }
  \"            { yylval->str = strdup(yyextra->getBuf()); yyextra->clearBuf();
                    yy_pop_state(yyscanner); return TK_STR;                      }
}

\|              { yy_push_state(PSYM, yyscanner); }

<PSYM>{
  [ ]           { yyextra->insertBuf(' ');                                       }
  [\t]          { yyextra->insertBuf('\t');                                      }
  \n            { yyextra->insertBuf('\n');                                      }
  [^ \t\n\\\|]  { yyextra->insertBuf(yyget_text(yyscanner)[0]);                  }
  \|            { yylval->str = strdup(yyextra->getBuf()); yyextra->clearBuf();
                    yy_pop_state(yyscanner); return TK_SYM;                      }
  \\            { printf("Syntax error at line %d near %s, \\ not allowed inside | ... |\n", yyget_lineno(yyscanner), yyget_text(yyscanner)); exit(1); }
}

.               { printf( "Syntax error at line %d near %s\n", yyget_lineno(yyscanner), yyget_text(yyscanner) ); exit( 1 ); }

%%

int Smt2newContext::init_scanner()
{
    if (is != NULL) {
        yylex_init_extra(this, &scanner);
        yyset_in(is, scanner);
    }
    else if (ib != NULL) {
        yylex_init(&scanner);
        yylex_init_extra(this, &scanner);
        yy_scan_string(ib, scanner);
    }
    else
        return -1;
    return 0;
}

void Smt2newContext::destroy_scanner()
{
    yylex_destroy(scanner);
}

