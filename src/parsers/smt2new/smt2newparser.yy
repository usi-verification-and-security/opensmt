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
%define api.prefix {smt2new}
%locations
%defines
%parse-param { Smt2newContext* context }
%lex-param { void* scanner }

%{
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <vector>
#include <string>

#include "smt2newcontext.h"
#include "smt2newparser.hh"
#include "smt2tokens.h"

using ASTNode_up = std::unique_ptr<ASTNode>;
using ASTVec = std::vector<ASTNode_up>;
using ASTVec_up = std::unique_ptr<ASTVec>;
using string_up = std::unique_ptr<std::string>;

std::unique_ptr<std::string> mkUniqueStr(std::string const & s) { return std::make_unique<std::string>(s); }

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
  std::vector<std::unique_ptr<ASTNode>> * snode_list;
  osmttokens::smt2token        tok;
}

%destructor { delete $$; } <str>
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

script: command_list { context->insertRoot(std::make_unique<ASTNode>(ASTType::CMDL_T, osmttokens::smt2token{osmttokens::t_none}, mkUniqueStr("main-script"), ASTVec_up($1))); };

symbol: TK_SYM
        { $$ = new ASTNode(ASTType::SYM_T, {osmttokens::t_none}, string_up($1)); }
    | TK_QSYM
        { $$ = new ASTNode(ASTType::QSYM_T, {osmttokens::t_none}, string_up($1)); }
    ;

command_list:
        { $$ = new ASTVec(); }
    | command_list command
        { (*$1).emplace_back(ASTNode_up($2)); $$ = $1; }
    ;

command: '(' TK_SETLOGIC symbol ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($3));
            $$ = new ASTNode(ASTType::CMD_T, $2, mkUniqueStr(""), std::move(tmp));
        }
    | '(' TK_SETOPTION option ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($3));
            $$ = new ASTNode(ASTType::CMD_T, $2, mkUniqueStr(""), std::move(tmp));
        }
    | '(' TK_SETINFO attribute ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($3));
            $$ = new ASTNode(ASTType::CMD_T, $2, mkUniqueStr(""), std::move(tmp));
        }
    | '(' TK_DECLARESORT symbol TK_NUM ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($3));
            tmp->push_back(std::make_unique<ASTNode>(ASTType::NUM_T, osmttokens::smt2token{osmttokens::t_none}, string_up($4)));
            $$ = new ASTNode(ASTType::CMD_T,
                             $2,
                             mkUniqueStr(""),
                             std::move(tmp));
        }
    | '(' TK_DEFINESORT symbol '(' symbol_list ')' sort ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($3));
            tmp->push_back(std::make_unique<ASTNode>(ASTType::SYML_T, osmttokens::smt2token{osmttokens::t_none}, mkUniqueStr(""), ASTVec_up($5)));
            tmp->push_back(ASTNode_up($7));
            $$ = new ASTNode(ASTType::CMD_T, $2, mkUniqueStr(""), std::move(tmp));
        }

    | '(' TK_DECLAREFUN symbol '(' sort_list ')' sort ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($3));
            tmp->push_back(std::make_unique<ASTNode>(ASTType::SORTL_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, ASTVec_up($5)));
            tmp->push_back(ASTNode_up($7));
            $$ = new ASTNode(ASTType::CMD_T, $2, nullptr, std::move(tmp));
        }
    | '(' TK_DECLARECONST const_val sort ')'
        {
            // todo: drop the second child?
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($3));
            tmp->push_back(std::make_unique<ASTNode>(ASTType::SORTL_T));
            tmp->push_back(ASTNode_up($4));
            $$ = new ASTNode(ASTType::CMD_T, $2, nullptr, std::move(tmp));
        }
    | '(' TK_DEFINEFUN symbol '(' sorted_var_list ')' sort term ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($3));
            tmp->push_back(std::make_unique<ASTNode>(ASTType::SVL_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, ASTVec_up($5)));
            tmp->push_back(ASTNode_up($7));
            tmp->push_back(ASTNode_up($8));
            $$ = new ASTNode(ASTType::CMD_T, $2, nullptr, std::move(tmp));
        }
    | '(' TK_PUSH TK_NUM ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::NUM_T, osmttokens::smt2token{osmttokens::t_none}, string_up($3)));
            $$ = new ASTNode(ASTType::CMD_T, $2, nullptr, std::move(tmp));
        }
    | '(' TK_POP TK_NUM ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::NUM_T, osmttokens::smt2token{osmttokens::t_none}, string_up($3)));
            $$ = new ASTNode(ASTType::CMD_T, $2, nullptr, std::move(tmp));
        }
    | '(' TK_ASSERT term ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($3));
            $$ = new ASTNode(ASTType::CMD_T, $2, nullptr, std::move(tmp));
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
            $$ = new ASTNode(ASTType::CMD_T, $2, nullptr, ASTVec_up($3));
        }
    | '(' TK_WRSTATE TK_STR ')'
        {
            // todo: TK_{WR,RD}STATE and TK_WRFUNS is not implemented and is not part of the standard
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::UATTR_T, osmttokens::smt2token{osmttokens::t_none}, string_up($3)));
            $$ = new ASTNode(ASTType::CMD_T, $2, nullptr, std::move(tmp));
        }
    | '(' TK_RDSTATE TK_STR ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::UATTR_T, osmttokens::smt2token{osmttokens::t_none}, string_up($3)));
            $$ = new ASTNode(ASTType::CMD_T, $2, nullptr, std::move(tmp));
        }
    | '(' TK_WRFUNS TK_STR ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::UATTR_T, osmttokens::smt2token{osmttokens::t_none}, string_up($3)));
            $$ = new ASTNode(ASTType::CMD_T, $2, nullptr, std::move(tmp));
        }
    | '(' TK_GETUNSATCORE ')'
        {
            $$ = new ASTNode(ASTType::CMD_T, $2);
        }
    | '(' TK_GETVALUE '(' term term_list ')' ')'
        {
            // todo: insert first $4 and then extend with $5?
            $$ = new ASTNode(ASTType::CMD_T, $2, nullptr, ASTVec_up($5));
            $$->children->insert($$->children->begin(), ASTNode_up($4));
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
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::UATTR_T, osmttokens::smt2token{osmttokens::t_none}, string_up($3)));
            $$ = new ASTNode(ASTType::CMD_T, $2, nullptr, std::move(tmp));
        }
    | '(' TK_GETOPTION predef_key ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::PATTR_T, osmttokens::smt2token{osmttokens::t_none}, string_up($3)));
            $$ = new ASTNode(ASTType::CMD_T, $2, nullptr, std::move(tmp));
        }
    | '(' TK_GETINFO info_flag ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($3));
            $$ = new ASTNode(ASTType::CMD_T, $2, nullptr, std::move(tmp));
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
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::UATTR_T, osmttokens::smt2token{osmttokens::t_none}, string_up($3)));
            $$ = new ASTNode(ASTType::CMD_T, $2, nullptr, std::move(tmp));
        }
    ;

attribute_list:
        { $$ = new ASTVec{}; }
    | attribute_list attribute
        { $1->emplace_back(ASTNode_up($2)); $$ = $1; }
    ;

attribute: TK_KEY
        { $$ = new ASTNode(ASTType::UATTR_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1)); }
    | TK_KEY attribute_value
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($2));
            $$ = new ASTNode(ASTType::UATTR_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1), std::move(tmp));
        }
    | predef_key
        { $$ = new ASTNode(ASTType::PATTR_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1)); }
    | predef_key attribute_value
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($2));
            $$ = new ASTNode(ASTType::PATTR_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1), std::move(tmp));
        }
    ;

attribute_value: spec_const
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($1));
            $$ = new ASTNode(ASTType::SPECC_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, std::move(tmp)); }
    | symbol
        {
            $$ = $1;
        }
    | '(' s_expr_list ')'
        {
            $$ = new ASTNode(ASTType::SEXPRL_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, ASTVec_up($2));
        }
    ;

identifier: symbol
        { $$ = $1; }
    | '(' '_' symbol numeral_list ')'
        {
            $$ = $3;
            $$->children = ASTVec_up($4);
        }
    ;

sort: identifier
      { $$ = $1; }
    | '(' identifier sort sort_list ')'
      {
        auto tmp = std::make_unique<ASTVec>();
        tmp->push_back(ASTNode_up($2));
        tmp->push_back(ASTNode_up($3));
        $$ = new ASTNode(ASTType::LID_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, std::move(tmp));
        for (auto & c : *$4) {
            $$->children->push_back(std::move(c));
        }
        delete $4;
      }
    ;

sort_list: sort_list sort
        { $1->emplace_back(ASTNode_up($2)); $$ = $1; }
    |
        { $$ = new ASTVec(); }
    ;

s_expr: spec_const
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($1));
            $$ = new ASTNode(ASTType::SPECC_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, std::move(tmp));
        }
    | symbol
        {
            $$ = $1;
        }
    | TK_KEY
        {
            $$ = new ASTNode(ASTType::UATTR_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1));
        }
    | '(' s_expr_list ')'
        {
            $$ = new ASTNode(ASTType::SEXPRL_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, ASTVec_up($2));
        }
    ;

s_expr_list:
        {
            $$ = new ASTVec();
        }
    | s_expr_list s_expr
        {
            $1->emplace_back(ASTNode_up($2));
            $$ = $1;
        }
    ;


spec_const: TK_NUM
        { $$ = new ASTNode(ASTType::NUM_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1)); }
    | TK_DEC
        { $$ = new ASTNode(ASTType::DEC_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1)); }
    | TK_HEX
        { $$ = new ASTNode(ASTType::HEX_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1)); }
    | TK_BIN
        { $$ = new ASTNode(ASTType::BIN_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1)); }
    | TK_STR
        { $$ = new ASTNode(ASTType::STR_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1)); }
    ;

const_val: symbol
        { $$ = $1; }
    | spec_const
        { $$ = $1; }
    ;

numeral_list: numeral_list TK_NUM
        { $1->emplace_back(std::make_unique<ASTNode>(ASTType::NUM_T, osmttokens::smt2token{osmttokens::t_none}, string_up($2))); $$ = $1; }
    | TK_NUM
        { $$ = new ASTVec(); $$->push_back(std::make_unique<ASTNode>(ASTType::NUM_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1))); }
    ;

qual_identifier: identifier
        { $$ = $1; }
    | '(' TK_AS identifier sort ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($3));
            tmp->push_back(ASTNode_up($4));
            $$ = new ASTNode(ASTType::AS_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, std::move(tmp));
        }
    ;

var_binding_list: var_binding
        { $$ = new ASTVec(); $$->push_back(ASTNode_up($1)); }
    | var_binding_list var_binding
        { $1->emplace_back(ASTNode_up($2)); $$ = $1; }
    ;

var_binding: '(' symbol term ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($3));
            $$ = new ASTNode(ASTType::VARB_T, osmttokens::smt2token{osmttokens::t_none}, mkUniqueStr($2->getValue()), std::move(tmp));
            delete $2;
        }
    ;

sorted_var_list:
        { $$ = new ASTVec(); }
    | sorted_var_list sorted_var
        { $1->emplace_back(ASTNode_up($2)); $$ = $1; }
    ;

sorted_var: '(' symbol sort ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($3));
            $$ = new ASTNode(ASTType::SV_T, osmttokens::smt2token{osmttokens::t_none}, mkUniqueStr($2->getValue()), std::move(tmp));
            delete $2;
        }

term_list:
        { $$ = new ASTVec(); }
    | term_list term
        { $1->emplace_back(ASTNode_up($2)); $$ = $1; }
    ;

term: spec_const
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($1));
            $$ = new ASTNode(ASTType::TERM_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, std::move(tmp));
        }
    | qual_identifier
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($1));
            $$ = new ASTNode(ASTType::QID_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, std::move(tmp));
        }
    | '(' qual_identifier term term_list ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($2));
            tmp->push_back(ASTNode_up($3));
            $$ = new ASTNode(ASTType::LQID_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, std::move(tmp));
            for (auto & c : (*$4)) {
                $$->children->emplace_back(std::move(c));
            }
            delete $4;
        }
    | '(' TK_LET '(' var_binding_list ')' term ')'
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::VARBL_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, ASTVec_up($4)));
            tmp->push_back(ASTNode_up($6));
            $$ = new ASTNode(ASTType::LET_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, std::move(tmp));
        }
    | '(' TK_FORALL '(' sorted_var_list ')' term ')'
        {
            // todo: AST traversal must ensure that sorted_var_list is non-empty
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::SVL_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, ASTVec_up($4)));
            tmp->push_back(ASTNode_up($6));
            $$ = new ASTNode(ASTType::FORALL_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, std::move(tmp));
        }
    | '(' TK_EXISTS '(' sorted_var_list ')' term ')'
        {
            // todo: AST traversal must ensure that sorted_var_list is non-empty
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::SVL_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, ASTVec_up($4)));
            tmp->push_back(ASTNode_up($6));
            $$ = new ASTNode(ASTType::EXISTS_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, std::move(tmp));
        }
    | '(' '!' term attribute_list ')'
        {
            // todo: AST traversal must ensure that attribute_list is non-empty
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($3));
            tmp->push_back(std::make_unique<ASTNode>(ASTType::GATTRL_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, ASTVec_up($4)));
            $$ = new ASTNode(ASTType::BANG_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, std::move(tmp));
        }
    ;

symbol_list:
        { $$ = new ASTVec(); }
    | symbol_list symbol
        { $1->emplace_back(ASTNode_up($2)); $$ = $1; }
    ;

b_value: symbol
        {
            std::string const & str = $1->getValue();
            if (str == "true" or str == "false") {
                $$ = new ASTNode(ASTType::BOOL_T, osmttokens::smt2token{osmttokens::t_none}, mkUniqueStr(str)); delete $1;
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
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($2));
            $$ = new ASTNode(ASTType::OPTION_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1), std::move(tmp));
        }
    | KW_EXPANDDEFINITIONS b_value
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($2));
            $$ = new ASTNode(ASTType::OPTION_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1), std::move(tmp));
        }
    | KW_INTERACTIVEMODE b_value
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($2));
            $$ = new ASTNode(ASTType::OPTION_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1), std::move(tmp));
        }
    | KW_PRODUCEPROOFS b_value
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($2));
            $$ = new ASTNode(ASTType::OPTION_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1), std::move(tmp));
        }
    | KW_PRODUCEUNSATCORES b_value
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($2));
            $$ = new ASTNode(ASTType::OPTION_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1), std::move(tmp));
        }
    | KW_PRODUCEMODELS b_value
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($2));
            $$ = new ASTNode(ASTType::OPTION_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1), std::move(tmp));
        }
    | KW_PRODUCEASSIGNMENTS b_value
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($2));
            $$ = new ASTNode(ASTType::OPTION_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1), std::move(tmp));
        }
    | KW_REGULAROUTPUTCHANNEL TK_STR
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::STR_T, osmttokens::smt2token{osmttokens::t_none}, string_up($2)));
            $$ = new ASTNode(ASTType::OPTION_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1), std::move(tmp));
        }
    | KW_DIAGNOSTICOUTPUTCHANNEL TK_STR
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::STR_T, osmttokens::smt2token{osmttokens::t_none}, string_up($2)));
            $$ = new ASTNode(ASTType::OPTION_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1), std::move(tmp));
        }
    | KW_RANDOMSEED TK_NUM
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::NUM_T, osmttokens::smt2token{osmttokens::t_none}, string_up($2)));
            $$ = new ASTNode(ASTType::OPTION_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1), std::move(tmp));
        }
    | KW_VERBOSITY TK_NUM
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::NUM_T, osmttokens::smt2token{osmttokens::t_none}, string_up($2)));
            $$ = new ASTNode(ASTType::OPTION_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1), std::move(tmp));
        }
    | attribute
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(ASTNode_up($1));
            $$ = new ASTNode(ASTType::OPTION_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, std::move(tmp));
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
        { $$ = new ASTNode(ASTType::INFO_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1)); }
    | KW_NAME
        { $$ = new ASTNode(ASTType::INFO_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1)); }
    | KW_AUTHORS
        { $$ = new ASTNode(ASTType::INFO_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1)); }
    | KW_VERSION
        { $$ = new ASTNode(ASTType::INFO_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1)); }
    | KW_STATUS
        { $$ = new ASTNode(ASTType::INFO_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1)); }
    | KW_REASONUNKNOWN
        { $$ = new ASTNode(ASTType::INFO_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1)); }
    | KW_ALLSTATISTICS
        { $$ = new ASTNode(ASTType::INFO_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1)); }
    | TK_KEY
        {
            auto tmp = std::make_unique<ASTVec>();
            tmp->push_back(std::make_unique<ASTNode>(ASTType::GATTR_T, osmttokens::smt2token{osmttokens::t_none}, string_up($1)));
            $$ = new ASTNode(ASTType::INFO_T, osmttokens::smt2token{osmttokens::t_none}, nullptr, std::move(tmp));
        }
    ;

%%

//=======================================================================================
// Auxiliary Routines

