/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

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


%option reentrant
%option bison-bridge
%option bison-locations
%option noyywrap
%option yylineno
%option stack
%option nounput
%option noinput
%option noyy_top_state

%{

#include <cstdio>
#include <cstdlib>
#include <vector>
#include <list>

#include "smt2tokens.h"
#include "smt2newcontext.h"
#include "smt2newparser.hh"

using namespace osmttokens;

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
"as"       { yyget_lval(yyscanner)->tok = { t_as }; return TK_AS;                            }

"DECIMAL"  { yyget_lval(yyscanner)->tok = { t_DECIMAL }; return TK_DECIMAL; }
"exists"   { yyget_lval(yyscanner)->tok = { t_exists }; return TK_EXISTS;  }
"forall"   { yyget_lval(yyscanner)->tok = { t_forall }; return TK_FORALL;  }
"let"      { yyget_lval(yyscanner)->tok = { t_let }; return TK_LET;     }
"NUMERAL"  { yyget_lval(yyscanner)->tok = { t_NUMERAL }; return TK_NUMERAL; }
"par"      { yyget_lval(yyscanner)->tok = { t_par }; return TK_PAR;     }
"STRING"   { yyget_lval(yyscanner)->tok = { t_STRING}; return TK_STRING;  }

"assert"           { yyget_lval(yyscanner)->tok = { t_assert }; return TK_ASSERT;        }
"check-sat"        { yyget_lval(yyscanner)->tok = { t_checksat }; return TK_CHECKSAT;      }
"declare-sort"     { yyget_lval(yyscanner)->tok = { t_declaresort }; return TK_DECLARESORT;   }
"declare-fun"      { yyget_lval(yyscanner)->tok = { t_declarefun }; return TK_DECLAREFUN;    }
"declare-const"    { yyget_lval(yyscanner)->tok = { t_declareconst} ; return TK_DECLARECONST; }
"define-sort"      { yyget_lval(yyscanner)->tok = { t_definesort }; return TK_DEFINESORT;    }
"define-fun"       { yyget_lval(yyscanner)->tok = { t_definefun }; return TK_DEFINEFUN;     }
"exit"             { yyget_lval(yyscanner)->tok = { t_exit }; return TK_EXIT;          }
"get-assertions"   { yyget_lval(yyscanner)->tok = { t_getassertions }; return TK_GETASSERTIONS; }
"get-assignment"   { yyget_lval(yyscanner)->tok = { t_getassignment }; return TK_GETASSIGNMENT; }
"get-info"         { yyget_lval(yyscanner)->tok = { t_getinfo }; return TK_GETINFO;       }
"get-option"       { yyget_lval(yyscanner)->tok = { t_getoption }; return TK_GETOPTION;     }
"get-proof"        { yyget_lval(yyscanner)->tok = { t_getproof }; return TK_GETPROOF;      }
"get-unsat-core"   { yyget_lval(yyscanner)->tok = { t_getunsatcore }; return TK_GETUNSATCORE;  }
"get-value"        { yyget_lval(yyscanner)->tok = { t_getvalue }; return TK_GETVALUE;      }
"get-model"        { yyget_lval(yyscanner)->tok = { t_getmodel }; return TK_GETMODEL;      }
"pop"              { yyget_lval(yyscanner)->tok = { t_pop }; return TK_POP;           }
"push"             { yyget_lval(yyscanner)->tok = { t_push }; return TK_PUSH;          }
"set-logic"        { yyget_lval(yyscanner)->tok = { t_setlogic }; return TK_SETLOGIC;      }
"set-info"         { yyget_lval(yyscanner)->tok = { t_setinfo }; return TK_SETINFO;       }
"set-option"       { yyget_lval(yyscanner)->tok = { t_setoption }; return TK_SETOPTION;     }
"get-interpolants" { yyget_lval(yyscanner)->tok = { t_getinterpolants }; return TK_GETITPS;       }
"theory"           { yyget_lval(yyscanner)->tok = { t_theory }; return TK_THEORY;        }
"write-state"      { yyget_lval(yyscanner)->tok = { t_writestate }; return TK_WRSTATE;       }
"read-state"       { yyget_lval(yyscanner)->tok = { t_readstate }; return TK_RDSTATE;       }
"simplify"         { yyget_lval(yyscanner)->tok = { t_simplify }; return TK_SIMPLIFY;      }
"echo"             { yyget_lval(yyscanner)->tok = { t_echo }; return TK_ECHO; }

":sorts"                     { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_SORTS;                   }
":funs"                      { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_FUNS;                    }
":sorts-description"         { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_SORTSDESCRIPTION;        }
":funs-description"          { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_FUNSDESCRIPTION;         }
":definition"                { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_DEFINITION;              }
":values"                    { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_VALUES;                  }
":notes"                     { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_NOTES;                   }
":theories"                  { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_THEORIES;                }
":extensions"                { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_EXTENSIONS;              }
":print-success"             { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_PRINTSUCCESS;            }
":expand-definitions"        { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_EXPANDDEFINITIONS;       }
":interactive-mode"          { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_INTERACTIVEMODE;         }
":produce-proofs"            { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_PRODUCEPROOFS;           }
":produce-unsat-cores"       { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_PRODUCEUNSATCORES;       }
":produce-models"            { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_PRODUCEMODELS;           }
":produce-assignments"       { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_PRODUCEASSIGNMENTS;      }
":regular-output-channel"    { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_REGULAROUTPUTCHANNEL;    }
":diagnostic-output-channel" { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_DIAGNOSTICOUTPUTCHANNEL; }
":random-seed"               { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_RANDOMSEED;              }
":verbosity"                 { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_VERBOSITY;               }
":error-behavior"            { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_ERRORBEHAVIOR;           }
":name"                      { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_NAME;                    }
":named"                     { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_NAMED;                   }
":authors"                   { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_AUTHORS;                 }
":version"                   { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_VERSION;                 }
":status"                    { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_STATUS;                  }
":reason-unknown"            { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_REASONUNKNOWN;           }
":all-statistics"            { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return KW_ALLSTATISTICS;           }


0|-?[1-9][0-9]*(\/[1-9][0-9]*)? { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return TK_INT; }
-?[0-9]+\.0*[0-9]+              { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return TK_DEC; }
#x[0-9a-fA-F]+                  { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return TK_HEX; }
#b[01]+                         { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return TK_BIN; }

[a-zA-Z~!@\$\%\^&\*\-\+=\<\>\.\?\/'_][a-zA-Z0-9~!@\$\%\^&\*_\-\+=\<\>\.\?\/']* { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return TK_SYM; }
\:[a-zA-Z0-9~!@\$\%\^&\*_\-\+=\<\>\.\?\/]+ { yyget_lval(yyscanner)->str = new std::string(yyget_text(yyscanner)); return TK_KEY; }

[()]            { return *yyget_text(yyscanner); }

\"              { yy_push_state(STR, yyscanner); }

<STR>{
  [ ]           { yyextra->insertBuf(' ');                                       }
  [\t]          { yyextra->insertBuf('\t');                                      }
  \n            { yyextra->insertBuf('\n');                                      }
  \\\"          { yyextra->insertBuf('"');                                       }
  \\\\          { yyextra->insertBuf('\\');                                      }
  [^\\\n\"]     { yyextra->insertBuf(yyget_text(yyscanner)[0]);                  }
  \"            { yylval->str = new std::string(yyextra->getBuf()); yyextra->clearBuf();
                    yy_pop_state(yyscanner); return TK_STR;                      }
}

\|              { yy_push_state(PSYM, yyscanner); }

<PSYM>{
  [ ]           { yyextra->insertBuf(' ');                                       }
  [\t]          { yyextra->insertBuf('\t');                                      }
  \n            { yyextra->insertBuf('\n');                                      }
  [^ \t\n\\\|]  { yyextra->insertBuf(yyget_text(yyscanner)[0]);                  }
  \|            { yylval->str = new std::string(yyextra->getBuf()); yyextra->clearBuf();
                    yy_pop_state(yyscanner); return TK_QSYM;                     }
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

