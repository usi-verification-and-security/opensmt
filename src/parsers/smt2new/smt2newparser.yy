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
%lex-param { void * myScanner }
%define parse.error verbose
%code provides
{
  // Tell Flex the expected prototype of yylex.
  //#define YY_DECL int smt2newlex (SMT2NEWSTYPE *yylval, SMT2NEWLTYPE *yylloc)
  // Declare the scanner.
  //YY_DECL;

  int yylex(YYSTYPE* lvalp, YYLTYPE* llocp, void * myScanner);

  inline void yyerror(YYLTYPE* locp, Smt2newContext* context, const char * s ) {
    if (context->interactive)
      printf("At interactive input: %s\n", s);
    else
      printf("At line %d: %s\n", locp->first_line, s);
  }

  #define myScanner context->scanner
}

%locations
%defines
%parse-param { Smt2newContext* context }

%{
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <vector>
#include <string>

#include "smt2newcontext.h"
#include "smt2tokens.h"

using ASTNode_up = std::unique_ptr<ASTNode>;
using ASTVec = std::vector<ASTNode_up>;
using ASTVec_up = std::unique_ptr<ASTVec>;
using string_up = std::unique_ptr<std::string>;

std::unique_ptr<std::string> mkUniqueStr(std::string const & s) { return std::make_unique<std::string>(s); }


/* Overallocation to prevent stack overflow */
#define YYMAXDEPTH 1024 * 1024
%}

%union
{
  SortNode * n_sort;
  IdentifierNode * n_identifier;
  QualIdentifierNode * n_qualIdentifier;
  VarBindingNode * n_varBinding;
  std::vector<VarBindingNode> * n_varBindingList;
  std::vector<SortNode*> * n_sortList;
  std::vector<std::string> * n_numeralList;
  AttributeNode * n_attribute;
  AttributeValueNode * n_attributeValue;
  SpecConstNode * n_specConst;
  SExpr * sexpr;
  SymbolNode * n_symbol;
  CommandNode * n_command;
  TermNode * n_term;
  SortedVarNode * n_sortedVar;
  std::vector<SortedVarNode> * n_sortedVarList;
  std::vector<TermNode*> * n_termList;
  std::vector<AttributeNode> * n_attributeList;
  std::vector<CommandNode *> * n_commandList;
  std::vector<SymbolNode> * n_symbolList;
  std::vector<SExpr*> * sexpr_list;
  std::string * str;
  bool n_bool;
  OptionNode * n_option;
  ASTNode * snode;
  std::vector<std::unique_ptr<ASTNode>> * snode_list;
  osmttokens::smt2token tok;
}

%destructor { delete $$; } <str>

%token TK_AS TK_DECIMAL TK_EXISTS TK_FORALL TK_LET TK_NUMERAL TK_PAR TK_STRING
%token TK_ASSERT TK_CHECKSAT TK_DECLARESORT TK_DECLAREFUN TK_DECLARECONST TK_DEFINESORT TK_DEFINEFUN TK_EXIT TK_GETASSERTIONS TK_GETASSIGNMENT TK_GETINFO TK_GETOPTION TK_GETPROOF TK_GETUNSATCORE TK_GETVALUE TK_GETMODEL TK_POP TK_PUSH TK_SETLOGIC TK_SETINFO TK_SETOPTION TK_THEORY TK_GETITPS TK_WRSTATE TK_RDSTATE TK_SIMPLIFY TK_WRFUNS TK_ECHO
%token TK_NUM TK_SYM TK_QSYM TK_KEY TK_STR TK_DEC TK_HEX TK_BIN
%token KW_SORTS KW_FUNS KW_SORTSDESCRIPTION KW_FUNSDESCRIPTION KW_DEFINITION KW_NOTES KW_THEORIES KW_EXTENSIONS KW_VALUES KW_PRINTSUCCESS KW_EXPANDDEFINITIONS KW_INTERACTIVEMODE KW_PRODUCEPROOFS KW_PRODUCEUNSATCORES KW_PRODUCEMODELS KW_PRODUCEASSIGNMENTS KW_REGULAROUTPUTCHANNEL KW_DIAGNOSTICOUTPUTCHANNEL KW_RANDOMSEED KW_VERBOSITY KW_ERRORBEHAVIOR KW_NAME KW_NAMED KW_AUTHORS KW_VERSION KW_STATUS KW_REASONUNKNOWN KW_ALLSTATISTICS

%type <tok> TK_AS TK_DECIMAL TK_EXISTS TK_FORALL TK_LET TK_NUMERAL TK_PAR TK_STRING
%type <tok> TK_ASSERT TK_CHECKSAT TK_DECLARESORT TK_DECLAREFUN TK_DECLARECONST TK_DEFINESORT TK_DEFINEFUN TK_EXIT TK_GETASSERTIONS TK_GETASSIGNMENT TK_GETINFO TK_GETOPTION TK_GETPROOF TK_GETUNSATCORE TK_GETVALUE TK_GETMODEL TK_POP TK_PUSH TK_SETLOGIC TK_SETINFO TK_SETOPTION TK_THEORY TK_GETITPS TK_WRSTATE TK_RDSTATE TK_SIMPLIFY TK_WRFUNS TK_ECHO

%type <str> TK_NUM TK_SYM TK_QSYM TK_KEY TK_STR TK_DEC TK_HEX TK_BIN
%type <str> KW_SORTS KW_FUNS KW_SORTSDESCRIPTION KW_FUNSDESCRIPTION KW_DEFINITION KW_NOTES KW_THEORIES KW_EXTENSIONS KW_VALUES KW_PRINTSUCCESS KW_EXPANDDEFINITIONS KW_INTERACTIVEMODE KW_PRODUCEPROOFS KW_PRODUCEUNSATCORES KW_PRODUCEMODELS KW_PRODUCEASSIGNMENTS KW_REGULAROUTPUTCHANNEL KW_DIAGNOSTICOUTPUTCHANNEL KW_RANDOMSEED KW_VERBOSITY KW_ERRORBEHAVIOR KW_NAME KW_NAMED KW_AUTHORS KW_VERSION KW_STATUS KW_REASONUNKNOWN KW_ALLSTATISTICS predef_key
%type <n_sort> sort
%type <n_identifier> identifier
%type <n_qualIdentifier> qual_identifier
%type <n_varBinding> var_binding
%type <n_term> term
%type <n_sortedVar> sorted_var
%type <n_command> command
%type <n_symbol> symbol const_val
%type <sexpr> s_expr
%type <n_specConst> spec_const
%type <n_attribute> attribute
%type <n_attributeValue> attribute_value
%type <n_sortList> sort_list
%type <n_varBindingList> var_binding_list
%type <n_termList> term_list
%type <n_attributeList> attribute_list
%type <n_sortedVarList> sorted_var_list
%type <n_symbolList> symbol_list
%type <n_commandList> command_list
%type <sexpr_list> s_expr_list
%type <n_numeralList> numeral_list
%type <n_bool> b_value
%type <str> info_flag
%type <n_option> option

%start script

%%

script: command_list { context->insertRoot(std::move(*$1)); };

symbol: TK_SYM
        { $$ = new SymbolNode{{}, {std::move(*$1)}, false}; }
    | TK_QSYM
        { $$ = new SymbolNode {{}, {std::move(*$1)}, true}; }
    ;

command_list:
        { $$ = new std::vector<CommandNode*>(); }
    | command_list command
        { (*$1).emplace_back($2); $$ = $1; }
    ;

command: '(' TK_SETLOGIC symbol ')'
        { $$ = new SetLogic {{}, std::move(*$3)}; }
    | '(' TK_SETOPTION option ')'
        { $$ = new SetOption {{}, std::move(*$3)}; }
    | '(' TK_SETINFO attribute ')'
        { $$ = new SetInfo {{}, std::move(*$3)}; }
    | '(' TK_DECLARESORT symbol TK_NUM ')'
        { $$ = new DeclareSort {{}, std::move(*$3), std::move(*$4)}; }
    | '(' TK_DEFINESORT symbol '(' symbol_list ')' sort ')'
        { $$ = new DefineSort {{}, std::move(*$3), std::move(*$5), std::move(*$7)}; }
    | '(' TK_DECLAREFUN symbol '(' sort_list ')' sort ')'
        { $$ = new DeclareFun {{}, std::move(*$3), std::move(*$5), std::move(*$7)}; }
    | '(' TK_DECLARECONST const_val sort ')'
        { $$ = new DeclareConst {{}, std::move(*$3), std::move(*$4)}; }
    | '(' TK_DEFINEFUN symbol '(' sorted_var_list ')' sort term ')'
        { $$ = new DefineFun {{}, std::move(*$3), std::move(*$5), std::move(*$7), std::move(*$8)}; }
    | '(' TK_PUSH TK_NUM ')'
        { $$ = new PushNode {{}, std::stoi(*$3)}; delete $3; }
    | '(' TK_POP TK_NUM ')'
        { $$ = new PopNode {{}, std::stoi(*$3)}; delete $3; }
    | '(' TK_ASSERT term ')'
        { $$ = new AssertNode{{}, std::move(*$3)}; }
    | '(' TK_CHECKSAT ')'
        { $$ = new CheckSatNode(); }
    | '(' TK_GETASSERTIONS ')'
        { $$ = new GetAssertions(); }
    | '(' TK_GETPROOF ')'
        { $$ = new GetProof() ; }
    | '(' TK_GETITPS term_list ')'
        { $$ = new GetInterpolants {{}, std::move(*$3)}; }
    | '(' TK_GETUNSATCORE ')'
        { $$ = new GetUnsatCore(); }
    | '(' TK_GETVALUE '(' term_list ')' ')'
        { $$ = new GetValue { {}, std::move(*$4) }; }
    | '(' TK_GETMODEL ')'
            { $$ = new GetModel(); }
    | '(' TK_GETASSIGNMENT ')'
        { $$ = new GetAssignment(); }
    | '(' TK_GETOPTION TK_KEY ')'
        { $$ = new GetOption{ {}, std::move(*$3) }; }
    | '(' TK_GETOPTION predef_key ')'
        { $$ = new GetOption{ {}, std::move(*$3) }; }
    | '(' TK_GETINFO info_flag ')'
        { $$ = new GetInfo{ {}, std::move(*$3) }; }
    | '(' TK_SIMPLIFY ')'
        { $$ = new Simplify(); }
    | '(' TK_EXIT ')'
        { $$ = new Exit(); }
    | '(' TK_ECHO TK_STR ')'
        { $$ = new Echo{ {}, std::move(*$3) }; }
    ;

attribute_list:
        { $$ = new std::vector<AttributeNode>(); }
    | attribute_list attribute
        { $1->emplace_back(std::move(*$2)); $$ = $1; }
    ;

attribute: TK_KEY
        { $$ = new AttributeNode { {}, false, std::move(*$1), {{}, std::vector<SExpr*>{}} }; }
    | TK_KEY attribute_value
        { $$ = new AttributeNode { {}, false, std::move(*$1), std::move(*$2) }; }
    | predef_key
        { $$ = new AttributeNode { {}, true, std::move(*$1), {{}, std::vector<SExpr*>{}} }; }
    | predef_key attribute_value
        { $$ = new AttributeNode { {}, true, std::move(*$1), std::move(*$2) }; }
    ;

attribute_value: spec_const
        { $$ = new AttributeValueNode {{}, std::move(*$1)}; }
    | symbol
        { $$ = new AttributeValueNode {{}, std::move(*$1)}; }
    | '(' s_expr_list ')'
        { $$ = new AttributeValueNode {{}, std::move(*$2)}; }
    ;

identifier: symbol
        { $$ = new IdentifierNode {{}, std::move(*$1), {}}; }
    | '(' '_' symbol numeral_list ')'
        { $$ = new IdentifierNode {{}, std::move(*$3), std::move(*$4)}; }
    ;

sort: identifier
      { $$ = new SortNode {{}, std::move(*$1)}; }
    | '(' identifier sort sort_list ')'
      { $$ = new ComplexSortNode {{{}, std::move(*$2)}, $3, std::move(*$4)}; }
    ;

sort_list: sort_list sort
        { $1->emplace_back($2); $$ = $1; }
    |
        { $$ = new std::vector<SortNode*>(); }
    ;

s_expr: spec_const
        { $$ = new SExpr{{}, std::move(*$1)}; }
    | symbol
        { $$ = new SExpr{{}, std::move(*$1)}; }
    | TK_KEY
        { $$ = new SExpr{{}, std::move(*$1)}; }
    | '(' s_expr_list ')'
        { $$ = new SExpr{{}, std::move(*$2)}; }
    ;

s_expr_list:
        { $$ = new std::vector<SExpr*>(); }
    | s_expr_list s_expr
        {
            $1->emplace_back($2);
            $$ = $1;
        }
    ;


spec_const: TK_NUM
        { $$ = new SpecConstNode{{}, ConstType::numeral, std::move(*$1)}; }
    | TK_DEC
        { $$ = new SpecConstNode{{}, ConstType::decimal, std::move(*$1)}; }
    | TK_HEX
        { $$ = new SpecConstNode{{}, ConstType::hexadecimal, std::move(*$1)}; }
    | TK_BIN
        { $$ = new SpecConstNode{{}, ConstType::binary, std::move(*$1)}; }
    | TK_STR
        { $$ = new SpecConstNode{{}, ConstType::string, std::move(*$1)}; }
    ;

const_val: symbol
        { $$ = $1; }
    | spec_const
        { $$ = new SymbolNode {{}, std::move(*$1), false}; }
    ;

numeral_list: numeral_list TK_NUM
        { $1->push_back(std::string(*$2)); delete $2; }
    | TK_NUM
        { $$ = new std::vector<std::string>{std::string(std::move(*$1))}; }
    ;

qual_identifier: identifier
        { $$ = new QualIdentifierNode {{}, std::move(*$1)}; }
    | '(' TK_AS identifier sort ')'
        { $$ = new QualIdentifierNode {{}, std::move(*$3), $4}; }
    ;

var_binding_list: var_binding
        { $$ = new std::vector<VarBindingNode>; $$->push_back(std::move(*$1)); }
    | var_binding_list var_binding
        { $1->emplace_back(std::move(*$2)); $$ = $1; }
    ;

var_binding: '(' symbol term ')'
        { $$ = new VarBindingNode { {}, std::move(*$2), std::move(*$3) }; }
    ;

sorted_var_list:
        { $$ = new std::vector<SortedVarNode>(); }
    | sorted_var_list sorted_var
        { $1->emplace_back(std::move(*$2)); $$ = $1; }
    ;

sorted_var: '(' symbol sort ')'
        { $$ = new SortedVarNode {{}, std::move(*$2), std::move(*$3)}; }

term_list:
        { $$ = new std::vector<TermNode*>(); }
    | term_list term
        { $1->emplace_back($2); $$ = $1; }
    ;

term: spec_const
        { $$ = new NormalTermNode {{}, std::move(*$1), nullptr, std::vector<TermNode*>{}}; }
    | qual_identifier
        { $$ = new NormalTermNode {{}, std::move($1->identifier), $1->returnSort, {}}; delete $1; }
    | '(' qual_identifier term term_list ')'
        {
            auto tmp = std::vector<TermNode*>();
            tmp.push_back($3);
            for (auto & c : (*$4)) {
                tmp.emplace_back(std::move(c));
            }
            delete $4;
            $$ = new NormalTermNode {{}, std::move($2->identifier), $2->returnSort, std::move(tmp)};
        }
    | '(' TK_LET '(' var_binding_list ')' term ')'
        { $$ = new LetTermNode {{}, std::move(*$6), std::move(*$4)}; }
    | '(' TK_FORALL '(' sorted_var_list ')' term ')' // todo: AST traversal must ensure that sorted_var_list is non-empty
        { $$ = new ForallNode {{}, std::move(*$6), std::move(*$4)}; }
    | '(' TK_EXISTS '(' sorted_var_list ')' term ')' // todo: AST traversal must ensure that sorted_var_list is non-empty
        { $$ = new ExistsNode {{}, std::move(*$6), std::move(*$4)}; }
    | '(' '!' term attribute_list ')' // todo: AST traversal must ensure that attribute_list is non-empty
        { $$ = new AnnotationNode {{}, std::move(*$3), std::move(*$4)}; }
    ;

symbol_list:
        { $$ = new std::vector<SymbolNode>(); }
    | symbol_list symbol
        { $1->emplace_back(std::move(*$2)); $$ = $1; }
    ;

b_value: symbol
        {
            if (std::string const * str_p = std::get_if<std::string>(&($1->name))) {
                if (*str_p == "true") {
                    $$ = true;
                } else if (*str_p == "false") {
                    $$ = false;
                } else {
                    printf("Syntax error: expecting either 'true' or 'false', got '%s'\n", str_p->c_str());
                    delete $1;
                    YYERROR;
                }
                delete $1;
            } else {
                SpecConstNode const * node = std::get_if<SpecConstNode>(&($1->name));
                assert(node);
                printf("Syntax error: expecting either 'true' or 'false', got '%s'\n", node->value.c_str());
                delete $1;
                YYERROR;
            }
        }
    ;

option: KW_PRINTSUCCESS b_value
        { $$ = new PrintSuccess {{}, $2}; (void)$1; }
    | KW_EXPANDDEFINITIONS b_value
        { $$ = new ExpandDefinitions {{}, $2}; (void)$1; }
    | KW_INTERACTIVEMODE b_value
        { $$ = new InteractiveMode {{}, $2}; (void)$1; }
    | KW_PRODUCEPROOFS b_value
        { $$ = new ProduceProofs {{}, $2}; (void)$1; }
    | KW_PRODUCEUNSATCORES b_value
        { $$ = new ProduceUnsatCores {{}, $2}; (void)$1; }
    | KW_PRODUCEMODELS b_value
        { $$ = new ProduceModels {{}, $2}; (void)$1; }
    | KW_PRODUCEASSIGNMENTS b_value
        { $$ = new ProduceAssignments {{}, $2}; (void)$1;}
    | KW_REGULAROUTPUTCHANNEL TK_STR
        { $$ = new RegularOutputChannel {{}, std::move(*$2)}; (void)$1; }
    | KW_DIAGNOSTICOUTPUTCHANNEL TK_STR
        { $$ = new DiagnosticOutputChannel {{}, std::move(*$2)}; (void)$1; }
    | KW_RANDOMSEED TK_NUM
        { $$ = new RandomSeed {{}, std::stoi(*$2) }; free $2; (void)$1; }
    | KW_VERBOSITY TK_NUM
        { $$ = new Verbosity {{}, std::stoi(*$2) }; free $2; (void)$1; }
    | attribute
        { $$ = new Attribute {{}, std::move(*$1) }; }
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
        { $$ = $1; }
    | KW_NAME
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
    | TK_KEY
        { $$ = $1; }
    ;

%%

//=======================================================================================
// Auxiliary Routines

