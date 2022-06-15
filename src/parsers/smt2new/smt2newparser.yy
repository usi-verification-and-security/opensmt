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


%define api.pure
%define parse.error verbose
%name-prefix "smt2new"
%locations
%defines
%parse-param { Smt2newContext* context }
%lex-param { void* scanner }

%{
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <vector>
#include <list>
#include <string>
#include <string.h>

#include "smt2newcontext.h"
#include "smt2newparser.hh"
#include "smt2tokens.h"

int smt2newlex(YYSTYPE* lvalp, YYLTYPE* llocp, void* scanner);

void smt2newerror( YYLTYPE* locp, Smt2newContext* context, const char * s )
{
  if (context->interactive)
    printf("At interactive input: %s\n", s);
  else
    printf( "At line %d: %s\n", locp->first_line, s );
//  exit( 1 );
}

#define scanner context->scanner

/* Overallocation to prevent stack overflow */
#define YYMAXDEPTH 1024 * 1024
%}

%union
{
  std::string *                str;
  ASTNode *                    snode;
  std::vector<ASTNode> *       snode_list;
  osmttokens::smt2token        tok;
}

%destructor { free($$); } <str>
%destructor { delete $$; } <snode>

%token TK_AS TK_DECIMAL TK_EXISTS TK_FORALL TK_LET TK_NUMERAL TK_PAR TK_STRING
%token TK_ASSERT TK_CHECKSAT TK_DECLARESORT TK_DECLAREFUN TK_DECLARECONST TK_DEFINESORT TK_DEFINEFUN TK_EXIT TK_GETASSERTIONS TK_GETASSIGNMENT TK_GETINFO TK_GETOPTION TK_GETPROOF TK_GETUNSATCORE TK_GETVALUE TK_GETMODEL TK_POP TK_PUSH TK_SETLOGIC TK_SETINFO TK_SETOPTION TK_THEORY TK_GETITPS TK_WRSTATE TK_RDSTATE TK_SIMPLIFY TK_WRFUNS TK_ECHO
%token TK_NUM TK_SYM TK_QSYM TK_KEY TK_STR TK_DEC TK_HEX TK_BIN
%token KW_SORTS KW_FUNS KW_SORTSDESCRIPTION KW_FUNSDESCRIPTION KW_DEFINITION KW_NOTES KW_THEORIES KW_EXTENSIONS KW_VALUES KW_PRINTSUCCESS KW_EXPANDDEFINITIONS KW_INTERACTIVEMODE KW_PRODUCEPROOFS KW_PRODUCEUNSATCORES KW_PRODUCEMODELS KW_PRODUCEASSIGNMENTS KW_REGULAROUTPUTCHANNEL KW_DIAGNOSTICOUTPUTCHANNEL KW_RANDOMSEED KW_VERBOSITY KW_ERRORBEHAVIOR KW_NAME KW_NAMED KW_AUTHORS KW_VERSION KW_STATUS KW_REASONUNKNOWN KW_ALLSTATISTICS

%type <tok> TK_AS TK_DECIMAL TK_EXISTS TK_FORALL TK_LET TK_NUMERAL TK_PAR TK_STRING
%type <tok> TK_ASSERT TK_CHECKSAT TK_DECLARESORT TK_DECLAREFUN TK_DECLARECONST TK_DEFINESORT TK_DEFINEFUN TK_EXIT TK_GETASSERTIONS TK_GETASSIGNMENT TK_GETINFO TK_GETOPTION TK_GETPROOF TK_GETUNSATCORE TK_GETVALUE TK_GETMODEL TK_POP TK_PUSH TK_SETLOGIC TK_SETINFO TK_SETOPTION TK_THEORY TK_GETITPS TK_WRSTATE TK_RDSTATE TK_SIMPLIFY TK_WRFUNS TK_ECHO

%type <str> TK_NUM TK_SYM TK_QSYM TK_KEY TK_STR TK_DEC TK_HEX TK_BIN
%type <str> KW_SORTS KW_FUNS KW_SORTSDESCRIPTION KW_FUNSDESCRIPTION KW_DEFINITION KW_NOTES KW_THEORIES KW_EXTENSIONS KW_VALUES KW_PRINTSUCCESS KW_EXPANDDEFINITIONS KW_INTERACTIVEMODE KW_PRODUCEPROOFS KW_PRODUCEUNSATCORES KW_PRODUCEMODELS KW_PRODUCEASSIGNMENTS KW_REGULAROUTPUTCHANNEL KW_DIAGNOSTICOUTPUTCHANNEL KW_RANDOMSEED KW_VERBOSITY KW_ERRORBEHAVIOR KW_NAME KW_NAMED KW_AUTHORS KW_VERSION KW_STATUS KW_REASONUNKNOWN KW_ALLSTATISTICS predef_key
%type <snode> symbol identifier sort command attribute attribute_value s_expr spec_const qual_identifier var_binding sorted_var term const_val
%type <snode_list> sort_list command_list s_expr_list numeral_list term_list var_binding_list attribute_list sorted_var_list symbol_list
%type <snode> b_value option info_flag

%start script

%%

script: command_list { ASTNode *n = new ASTNode(ASTType::CMDL_T, {osmttokens::t_none}, "main-script", std::move(*$1)); context->insertRoot(n); };

symbol: TK_SYM
        { $$ = new ASTNode(ASTType::SYM_T, {osmttokens::t_none}, std::move(*$1)); }
    | TK_QSYM
        { $$ = new ASTNode(ASTType::QSYM_T, {osmttokens::t_none}, std::move(*$1)); }
    ;

command_list:
        { $$ = new std::vector<ASTNode>(); }
    | command_list command
        { (*$1).push_back(std::move(*$2)); $$ = $1; }
    ;

command: '(' TK_SETLOGIC symbol ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2, "", std::vector<ASTNode>{std::move(*$3)});
        }
    | '(' TK_SETOPTION option ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2, "", std::vector<ASTNode>{std::move(*$3)});
        }
    | '(' TK_SETINFO attribute ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2, "", std::vector<ASTNode>{std::move(*$3)});
        }
    | '(' TK_DECLARESORT symbol TK_NUM ')'
        {
            $$ = new ASTNode(ASTType::CMD_T,
                             $2,
                             "",
                             std::vector<ASTNode>{std::move(*$3),
                                        ASTNode(ASTType::NUM_T, {osmttokens::t_none}, std::move(*$4))});
        }
    | '(' TK_DEFINESORT symbol '(' symbol_list ')' sort ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2, "",
                   std::vector<ASTNode>{
                        std::move(*$3),
                        ASTNode(ASTType::SYML_T, {osmttokens::t_none}, "", std::move(*$5)),
                        std::move(*$7)});
        }

    | '(' TK_DECLAREFUN symbol '(' sort_list ')' sort ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2, "",
                std::vector<ASTNode>{std::move(*$3),
                    ASTNode(ASTType::SORTL_T, {osmttokens::t_none}, "", std::move(*$5)),
                    std::move(*$7)});
        }
    | '(' TK_DECLARECONST const_val sort ')'
        {
            // todo: drop the second child?
            $$ = new ASTNode(ASTType::CMD_T, $2, "",
                    std::vector<ASTNode>{std::move(*$3), ASTNode(ASTType::SORTL_T), std::move(*$4)});
        }
    | '(' TK_DEFINEFUN symbol '(' sorted_var_list ')' sort term ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2, "",
                    std::vector<ASTNode>{std::move(*$3),
                                         ASTNode(ASTType::SVL_T, {osmttokens::t_none}, "", std::move(*$5)),
                                         std::move(*$7),
                                         std::move(*$8)});
        }
    | '(' TK_PUSH TK_NUM ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2, "", std::vector<ASTNode>{ASTNode(ASTType::NUM_T, {osmttokens::t_none}, std::move(*$3))});
        }
    | '(' TK_POP TK_NUM ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2, "", std::vector<ASTNode>{ASTNode(ASTType::NUM_T, {osmttokens::t_none}, std::move(*$3))});
        }
    | '(' TK_ASSERT term ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2, "", std::vector<ASTNode>{std::move(*$3)});
        }
    | '(' TK_CHECKSAT ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2);
        }
    | '(' TK_GETASSERTIONS ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2);
        }
    | '(' TK_GETPROOF ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2);
        }
    | '(' TK_GETITPS term_list ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2, "", std::move(*$3));
        }
    | '(' TK_WRSTATE TK_STR ')'
        {
            // todo: consider inserting the TK_STR to the string?
            // todo: TK_{WR,RD}STATE and TK_WRFUNS is not implemented and is not part of the standard
            $$ = new ASTNode(ASTType::CMD_T, $2, "", std::vector<ASTNode>{ASTNode(ASTType::UATTR_T, {osmttokens::t_none}, std::move(*$3))});
        }
    | '(' TK_RDSTATE TK_STR ')'
        {
            // todo: consider inserting the TK_STR to the string?
            $$ = new ASTNode(ASTType::CMD_T, $2, "", std::vector<ASTNode>{ASTNode(ASTType::UATTR_T, {osmttokens::t_none}, std::move(*$3))});
        }
    | '(' TK_WRFUNS TK_STR ')'
        {
            // todo: consider inserting the TK_STR to the string?
            $$ = new ASTNode(ASTType::CMD_T, $2, "", std::vector<ASTNode>{ASTNode(ASTType::UATTR_T, {osmttokens::t_none}, std::move(*$3))});
        }
    | '(' TK_GETUNSATCORE ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2);
        }
    | '(' TK_GETVALUE '(' term term_list ')' ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2, "", std::vector<ASTNode>{std::move(*$5)});
            $$->children.insert($$->children.begin(), std::move(*$4));
        }
    | '(' TK_GETMODEL ')'
            {
                $$ = new ASTNode(ASTType::CMD_T, $2);
            }
    | '(' TK_GETASSIGNMENT ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2);
        }
    | '(' TK_GETOPTION TK_KEY ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2, "", std::vector<ASTNode>{ASTNode(ASTType::UATTR_T, {osmttokens::t_none}, std::move(*$3))});
        }
    | '(' TK_GETOPTION predef_key ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2, "", std::vector<ASTNode>{ASTNode(ASTType::PATTR_T, {osmttokens::t_none}, std::move(*$3))});
        }
    | '(' TK_GETINFO info_flag ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2, "", std::vector<ASTNode>{std::move(*$3)});
        }
    | '(' TK_SIMPLIFY ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2);
        }
    | '(' TK_EXIT ')'
        { $$ = new ASTNode(ASTType::CMD_T, $2); }
    | '(' TK_ECHO TK_STR ')'
        {
            // todo: consider using ASTNode's string instead of vector
            $$ = new ASTNode(ASTType::CMD_T, $2, "", std::vector<ASTNode>{ASTNode(ASTType::UATTR_T, {osmttokens::t_none}, std::move(*$3))});
        }
    ;

attribute_list:
        { $$ = new std::vector<ASTNode>(); }
    | attribute_list attribute
        { $1->push_back(std::move(*$2)); $$ = $1; }
    ;

attribute: TK_KEY
        { $$ = new ASTNode(ASTType::UATTR_T, {osmttokens::t_none}, std::move(*$1)); }
    | TK_KEY attribute_value
        { $$ = new ASTNode(ASTType::UATTR_T, {osmttokens::t_none}, std::move(*$1), std::vector<ASTNode>{std::move(*$2)}); }
    | predef_key
        { $$ = new ASTNode(ASTType::PATTR_T, {osmttokens::t_none}, std::move(*$1)); }
    | predef_key attribute_value
        { $$ = new ASTNode(ASTType::PATTR_T, {osmttokens::t_none}, std::move(*$1), std::vector<ASTNode>{std::move(*$2)}); }
    ;

attribute_value: spec_const
        { $$ = new ASTNode(ASTType::SPECC_T, {osmttokens::t_none}, "", std::vector<ASTNode>{std::move(*$1)}); }
    | symbol
        {
            $$ = $1;
        }
    | '(' s_expr_list ')'
        {
            $$ = new ASTNode(ASTType::SEXPRL_T, {osmttokens::t_none}, "", std::vector<ASTNode>{std::move(*$2)});
        }
    ;

identifier: symbol
        { $$ = $1; }
    | '(' '_' symbol numeral_list ')'
        {
            $$ = $3;
            for (auto & el : *$4) {
                $$->children.emplace_back(std::move(el));
            }
        }
    ;

sort: identifier
      { $$ = $1; }
    | '(' identifier sort sort_list ')'
      {
        $$ = new ASTNode(ASTType::LID_T, {osmttokens::t_none}, "", std::vector<ASTNode>{std::move(*$2), std::move(*$3)});
        for (auto & c : *$4) {
            $$->children.push_back(std::move(c));
        }
      }
    ;

sort_list: sort_list sort
        { $1->push_back(std::move(*$2)); $$ = $1; }
    |
        { $$ = new std::vector<ASTNode>(); }
    ;

s_expr: spec_const
        {
            $$ = new ASTNode(ASTType::SPECC_T, {osmttokens::t_none}, "", std::vector<ASTNode>{std::move(*$1)});
        }
    | symbol
        {
            $$ = $1;
        }
    | TK_KEY
        {
            $$ = new ASTNode(ASTType::UATTR_T, {osmttokens::t_none}, std::move(*$1));
        }
    | '(' s_expr_list ')'
        {
            $$ = new ASTNode(ASTType::SEXPRL_T, {osmttokens::t_none}, "", std::move(*$2));
        }
    ;

s_expr_list:
        {
            $$ = new std::vector<ASTNode>();
        }
    | s_expr_list s_expr
        {
            $1->push_back(std::move(*$2));
            $$ = $1;
        }
    ;


spec_const: TK_NUM
        { $$ = new ASTNode(ASTType::NUM_T, {osmttokens::t_none}, std::move(*$1)); }
    | TK_DEC
        { $$ = new ASTNode(ASTType::DEC_T, {osmttokens::t_none}, std::move(*$1)); }
    | TK_HEX
        { $$ = new ASTNode(ASTType::HEX_T, {osmttokens::t_none}, std::move(*$1)); }
    | TK_BIN
        { $$ = new ASTNode(ASTType::BIN_T, {osmttokens::t_none}, std::move(*$1)); }
    | TK_STR
        { $$ = new ASTNode(ASTType::STR_T, {osmttokens::t_none}, std::move(*$1)); }
    ;

const_val: symbol
        { $$ = $1; }
    | spec_const
        { $$ = $1; }
    ;

numeral_list: numeral_list TK_NUM
        { $1->push_back(ASTNode(ASTType::NUM_T, {osmttokens::t_none}, std::move(*$2))); $$ = $1; }
    | TK_NUM
        { $$ = new std::vector<ASTNode>{ASTNode(ASTType::NUM_T, {osmttokens::t_none}, std::move(*$1))}; }
    ;

qual_identifier: identifier
        { $$ = $1; }
    | '(' TK_AS identifier sort ')'
        {
            $$ = new ASTNode(ASTType::AS_T, {osmttokens::t_none}, "", std::vector<ASTNode>{std::move(*$3), std::move(*$4)});
        }
    ;

var_binding_list: var_binding
        { $$ = new std::vector<ASTNode>{std::move(*$1)}; }
    | var_binding_list var_binding
        { $1->push_back(std::move(*$2)); $$ = $1; }
    ;

var_binding: '(' symbol term ')'
        { $$ = new ASTNode(ASTType::VARB_T, {osmttokens::t_none}, std::string($2->getValue()), std::vector<ASTNode>{std::move(*$3)}); }
    ;

sorted_var_list:
        { $$ = new std::vector<ASTNode>(); }
    | sorted_var_list sorted_var
        { $1->push_back(std::move(*$2)); $$ = $1; }
    ;

sorted_var: '(' symbol sort ')'
        { $$ = new ASTNode(ASTType::SV_T, {osmttokens::t_none}, std::string($2->getValue()), std::vector<ASTNode>{std::move(*$3)}); }

term_list:
        { $$ = new std::vector<ASTNode>(); }
    | term_list term
        { $1->push_back(std::move(*$2)); $$ = $1; }
    ;

term: spec_const
        { $$ = new ASTNode(ASTType::TERM_T, {osmttokens::t_none}, "", std::vector<ASTNode>{std::move(*$1)}); }
    | qual_identifier
        { $$ = new ASTNode(ASTType::QID_T, {osmttokens::t_none}, "", std::vector<ASTNode>{std::move(*$1)}); }
    | '(' qual_identifier term term_list ')'
        {
            $$ = new ASTNode(ASTType::LQID_T, {osmttokens::t_none}, "", std::vector<ASTNode>{std::move(*$2), std::move(*$3)});
            for (auto & c : (*$4)) {
                $$->children.push_back(std::move(c));
            }
        }
    | '(' TK_LET '(' var_binding_list ')' term ')'
        {
            $$ = new ASTNode(ASTType::LET_T, {osmttokens::t_none}, "", {ASTNode(ASTType::VARBL_T, {osmttokens::t_none}, "", std::move(*$4)), std::move(*$6)});
        }
    | '(' TK_FORALL '(' sorted_var_list ')' term ')'
        {
            // todo: AST traversal must ensure that sorted_var_list is non-empty
            $$ = new ASTNode(ASTType::FORALL_T, {osmttokens::t_none}, "", {ASTNode(ASTType::SVL_T, {osmttokens::t_none}, "", std::move(*$4)), std::move(*$6)});
        }
    | '(' TK_EXISTS '(' sorted_var_list ')' term ')'
        {
            // todo: AST traversal must ensure that sorted_var_list is non-empty
            $$ = new ASTNode(ASTType::EXISTS_T, {osmttokens::t_none}, "", {ASTNode(ASTType::SVL_T, {osmttokens::t_none}, "", std::move(*$4)), std::move(*$6)});
        }
    | '(' '!' term attribute_list ')'
        {
            // todo: AST traversal must ensure that attribute_list is non-empty
            $$ = new ASTNode(ASTType::BANG_T, {osmttokens::t_none}, "", {std::move(*$3), ASTNode(ASTType::GATTRL_T, {osmttokens::t_none}, "", std::move(*$4))});
        }
    ;

symbol_list:
        { $$ = new std::vector<ASTNode>(); }
    | symbol_list symbol
        { $1->push_back(*$2); $$ = $1; }
    ;

b_value: symbol
        {
            std::string const & str = $1->getValue();
            if (str == "true" or str == "false") {
                $$ = new ASTNode(ASTType::BOOL_T, {osmttokens::t_none}, std::string(str)); delete $1;
            }
            else {
                printf("Syntax error: expecting either 'true' or 'false', got '%s'\n", str.c_str());
                delete $1;
                YYERROR;
            }
        }
    ;

option: KW_PRINTSUCCESS b_value
        {
            $$ = new ASTNode(ASTType::OPTION_T, {osmttokens::t_none}, std::move(*$1), std::vector<ASTNode>{std::move(*$2)});
        }
    | KW_EXPANDDEFINITIONS b_value
        {
            $$ = new ASTNode(ASTType::OPTION_T, {osmttokens::t_none}, std::move(*$1), std::vector<ASTNode>{std::move(*$2)});
        }
    | KW_INTERACTIVEMODE b_value
        {
            $$ = new ASTNode(ASTType::OPTION_T, {osmttokens::t_none}, std::move(*$1), std::vector<ASTNode>{std::move(*$2)});
        }
    | KW_PRODUCEPROOFS b_value
        {
            $$ = new ASTNode(ASTType::OPTION_T, {osmttokens::t_none}, std::move(*$1), std::vector<ASTNode>{std::move(*$2)});
        }
    | KW_PRODUCEUNSATCORES b_value
        {
            $$ = new ASTNode(ASTType::OPTION_T, {osmttokens::t_none}, std::move(*$1), std::vector<ASTNode>{std::move(*$2)});
        }
    | KW_PRODUCEMODELS b_value
        {
            $$ = new ASTNode(ASTType::OPTION_T, {osmttokens::t_none}, std::move(*$1), std::vector<ASTNode>{std::move(*$2)});
        }
    | KW_PRODUCEASSIGNMENTS b_value
        {
            $$ = new ASTNode(ASTType::OPTION_T, {osmttokens::t_none}, std::move(*$1), std::vector<ASTNode>{std::move(*$2)});
        }
    | KW_REGULAROUTPUTCHANNEL TK_STR
        {
            $$ = new ASTNode(ASTType::OPTION_T, {osmttokens::t_none}, std::move(*$1), std::vector<ASTNode>{ASTNode(ASTType::STR_T, {osmttokens::t_none}, std::move(*$2))});
        }
    | KW_DIAGNOSTICOUTPUTCHANNEL TK_STR
        {
            $$ = new ASTNode(ASTType::OPTION_T, {osmttokens::t_none}, std::move(*$1), std::vector<ASTNode>{ASTNode(ASTType::STR_T, {osmttokens::t_none}, std::move(*$2))});
        }
    | KW_RANDOMSEED TK_NUM
        {
            $$ = new ASTNode(ASTType::OPTION_T, {osmttokens::t_none}, std::move(*$1), std::vector<ASTNode>{ASTNode(ASTType::NUM_T, {osmttokens::t_none}, std::move(*$2))});
        }
    | KW_VERBOSITY TK_NUM
        {
            $$ = new ASTNode(ASTType::OPTION_T, {osmttokens::t_none}, std::move(*$1), std::vector<ASTNode>{ASTNode(ASTType::NUM_T, {osmttokens::t_none}, std::move(*$2))});
        }
    | attribute
        {
            $$ = new ASTNode(ASTType::OPTION_T, {osmttokens::t_none}, "", std::vector<ASTNode>{std::move(*$1)});
        }
    ;

predef_key: KW_SORTS
        { $$ = $1; }
    | KW_FUNS
        { $$ = $1; }
    | KW_SORTSDESCRIPTION
        { $$ = $1; }
    | KW_FUNSDESCRIPTION
        { $$ = $1; }
    | KW_DEFINITION
        { $$ = $1; }
    | KW_VALUES
        { $$ = $1; }
    | KW_NOTES
        { $$ = $1; }
    | KW_THEORIES
        { $$ = $1; }
    | KW_EXTENSIONS
        { $$ = $1; }
    | KW_PRINTSUCCESS
        { $$ = $1; }
    | KW_EXPANDDEFINITIONS
        { $$ = $1; }
    | KW_INTERACTIVEMODE
        { $$ = $1; }
    | KW_PRODUCEPROOFS
        { $$ = $1; }
    | KW_PRODUCEUNSATCORES
        { $$ = $1; }
    | KW_PRODUCEMODELS
        { $$ = $1; }
    | KW_PRODUCEASSIGNMENTS
        { $$ = $1; }
    | KW_REGULAROUTPUTCHANNEL
        { $$ = $1; }
    | KW_DIAGNOSTICOUTPUTCHANNEL
        { $$ = $1; }
    | KW_RANDOMSEED
        { $$ = $1; }
    | KW_VERBOSITY
        { $$ = $1; }
    | KW_ERRORBEHAVIOR
        { $$ = $1; }
    | KW_NAME
        { $$ = $1; }
    | KW_NAMED
        { $$ = $1; }
    | KW_AUTHORS
        { $$ = $1; }
    | KW_VERSION
        { $$ = $1; }
    | KW_STATUS
        { $$ = $1; }
    | KW_REASONUNKNOWN
        { $$ = $1; }
    | KW_ALLSTATISTICS
        { $$ = $1; }
    ;

info_flag: KW_ERRORBEHAVIOR
        { $$ = new ASTNode(ASTType::INFO_T, {osmttokens::t_none}, std::move(*$1)); }
    | KW_NAME
        { $$ = new ASTNode(ASTType::INFO_T, {osmttokens::t_none}, std::move(*$1)); }
    | KW_AUTHORS
        { $$ = new ASTNode(ASTType::INFO_T, {osmttokens::t_none}, std::move(*$1)); }
    | KW_VERSION
        { $$ = new ASTNode(ASTType::INFO_T, {osmttokens::t_none}, std::move(*$1)); }
    | KW_STATUS
        { $$ = new ASTNode(ASTType::INFO_T, {osmttokens::t_none}, std::move(*$1)); }
    | KW_REASONUNKNOWN
        { $$ = new ASTNode(ASTType::INFO_T, {osmttokens::t_none}, std::move(*$1)); }
    | KW_ALLSTATISTICS
        { $$ = new ASTNode(ASTType::INFO_T, {osmttokens::t_none}, std::move(*$1)); }
    | TK_KEY
        { $$ = new ASTNode(ASTType::INFO_T, {osmttokens::t_none}, "", std::vector<ASTNode>{ASTNode(ASTType::GATTR_T, {osmttokens::t_none}, std::move(*$1))}); }
    ;

%%

//=======================================================================================
// Auxiliary Routines

