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
  std::vector<std::unique_ptr<VarBindingNode>> * n_varBindingList;
  std::vector<SortNode*> * n_sortList;
  std::vector<std::unique_ptr<std::string>> * n_numeralList;
  AttributeNode * n_attribute;
  AttributeValueNode * n_attributeValue;
  SpecConstNode * n_specConst;
  SExpr * sexpr;
  SymbolNode * n_symbol;
  CommandNode * n_command;
  TermNode * n_term;
  SortedVarNode * n_sortedVar;
  std::vector<std::unique_ptr<SortedVarNode>> * n_sortedVarList;
  std::vector<TermNode*> * n_termList;
  std::vector<std::unique_ptr<AttributeNode>> * n_attributeList;
  std::vector<CommandNode *> * n_commandList;
  std::vector<std::unique_ptr<SymbolNode>> * n_symbolList;
  std::vector<SExpr*> * sexpr_list;
  std::string * str;
  bool n_bool;
  OptionNode * n_option;
  osmttokens::smt2token tok;
}

%destructor { delete $$; } <n_attributeValue>
%destructor { delete $$; } <n_attribute>
%destructor { delete $$; } <n_attributeList>
%destructor { delete $$; } <n_command>
%destructor { for (CommandNode * n : *$$) { delete n; }; delete $$; } <n_commandList>
%destructor { delete $$; } <n_identifier>
%destructor { delete $$; } <n_numeralList>
%destructor { delete $$; } <n_qualIdentifier>
%destructor { delete $$; } <n_option>
%destructor { delete $$; } <n_sort>
%destructor { delete $$; } <n_sortedVar>
%destructor { delete $$; } <n_sortedVarList>
%destructor { for (SortNode * n : *$$) { delete n; }; delete $$; } <n_sortList>
%destructor { delete $$; } <n_specConst>
%destructor { delete $$; } <n_symbol>
%destructor { delete $$; } <n_symbolList>
%destructor { delete $$; } <n_term>
%destructor { for (TermNode * n : *$$) { delete n; }; delete $$; } <n_termList>
%destructor { delete $$->term; delete $$; } <n_varBinding>
%destructor { delete $$; } <n_varBindingList>
%destructor { delete $$; } <sexpr>
%destructor { for (SExpr * n : *$$) { delete n; }; delete $$; } <sexpr_list>
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

script: command_list { context->insertRoot(std::unique_ptr<std::vector<CommandNode*>>($1)); };

symbol: TK_SYM
        { $$ = new SymbolNode {{}, {std::unique_ptr<std::string>($1)}, false}; }
    | TK_QSYM
        { $$ = new SymbolNode {{}, {std::unique_ptr<std::string>($1)}, true}; }
    ;

command_list:
        { $$ = new std::vector<CommandNode*>(); }
    | command_list command
        { (*$1).emplace_back($2); $$ = $1; }
    ;

command: '(' TK_SETLOGIC symbol ')'
        { $$ = new SetLogic {std::unique_ptr<SymbolNode>($3)}; }
    | '(' TK_SETOPTION option ')'
        { $$ = new SetOption {std::unique_ptr<OptionNode>($3)}; }
    | '(' TK_SETINFO attribute ')'
        { $$ = new SetInfo {std::unique_ptr<AttributeNode>($3)}; }
    | '(' TK_DECLARESORT symbol TK_NUM ')'
        { $$ = new DeclareSort {std::unique_ptr<SymbolNode>($3), std::unique_ptr<std::string>($4)}; }
    | '(' TK_DEFINESORT symbol '(' symbol_list ')' sort ')'
        { $$ = new DefineSort {std::unique_ptr<SymbolNode>($3), std::unique_ptr<std::vector<std::unique_ptr<SymbolNode>>>($5), std::unique_ptr<SortNode>($7)}; }
    | '(' TK_DECLAREFUN symbol '(' sort_list ')' sort ')'
        { $$ = new DeclareFun {std::unique_ptr<SymbolNode>($3), std::unique_ptr<std::vector<SortNode*>>($5), std::unique_ptr<SortNode>($7)}; }
    | '(' TK_DECLARECONST const_val sort ')'
        { $$ = new DeclareConst {std::unique_ptr<SymbolNode>($3), std::unique_ptr<SortNode>($4)}; }
    | '(' TK_DEFINEFUN symbol '(' sorted_var_list ')' sort term ')'
        { $$ = new DefineFun {std::unique_ptr<SymbolNode>($3), std::unique_ptr<std::vector<std::unique_ptr<SortedVarNode>>>($5), std::unique_ptr<SortNode>($7), std::unique_ptr<TermNode>($8)}; }
    | '(' TK_PUSH TK_NUM ')'
        { $$ = new PushNode {std::stoi(*$3)}; delete $3; }
    | '(' TK_POP TK_NUM ')'
        { $$ = new PopNode {std::stoi(*$3)}; delete $3; }
    | '(' TK_ASSERT term ')'
        { $$ = new AssertNode{std::unique_ptr<TermNode>($3)}; }
    | '(' TK_CHECKSAT ')'
        { $$ = new CheckSatNode(); }
    | '(' TK_GETASSERTIONS ')'
        { $$ = new GetAssertions(); }
    | '(' TK_GETPROOF ')'
        { $$ = new GetProof() ; }
    | '(' TK_GETITPS term_list ')'
        { $$ = new GetInterpolants {std::unique_ptr<std::vector<TermNode*>>($3)}; }
    | '(' TK_GETUNSATCORE ')'
        { $$ = new GetUnsatCore(); }
    | '(' TK_GETVALUE '(' term_list ')' ')'
        { $$ = new GetValue {std::unique_ptr<std::vector<TermNode*>>($4)}; }
    | '(' TK_GETMODEL ')'
            { $$ = new GetModel(); }
    | '(' TK_GETASSIGNMENT ')'
        { $$ = new GetAssignment(); }
    | '(' TK_GETOPTION TK_KEY ')'
        { $$ = new GetOption{ std::unique_ptr<std::string>($3) }; }
    | '(' TK_GETOPTION predef_key ')'
        { $$ = new GetOption{ std::unique_ptr<std::string>($3) }; }
    | '(' TK_GETINFO info_flag ')'
        { $$ = new GetInfo{ std::unique_ptr<std::string>($3) }; }
    | '(' TK_SIMPLIFY ')'
        { $$ = new Simplify(); }
    | '(' TK_EXIT ')'
        { $$ = new Exit(); }
    | '(' TK_ECHO TK_STR ')'
        { $$ = new Echo{ std::unique_ptr<std::string>($3) }; }
    ;

attribute_list:
        { $$ = new std::vector<std::unique_ptr<AttributeNode>>(); }
    | attribute_list attribute
        { $1->emplace_back(std::move($2)); $$ = $1; }
    ;

attribute: TK_KEY
        { $$ = new AttributeNode { {}, false, std::unique_ptr<std::string>($1), std::make_unique<AttributeValueNode>(std::make_unique<std::vector<SExpr*>>()) }; }
    | TK_KEY attribute_value
        { $$ = new AttributeNode { {}, false, std::unique_ptr<std::string>($1), std::unique_ptr<AttributeValueNode>($2) }; }
    | predef_key
        { $$ = new AttributeNode { {}, true, std::unique_ptr<std::string>($1), std::make_unique<AttributeValueNode>(std::make_unique<std::vector<SExpr*>>()) }; }
    | predef_key attribute_value
        { $$ = new AttributeNode { {}, true, std::unique_ptr<std::string>($1), std::unique_ptr<AttributeValueNode>($2) }; }
    ;

attribute_value: spec_const
        { $$ = new AttributeValueNode(std::unique_ptr<SpecConstNode>($1)); }
    | symbol
        { $$ = new AttributeValueNode(std::unique_ptr<SymbolNode>($1)); }
    | '(' s_expr_list ')'
        { $$ = new AttributeValueNode(std::unique_ptr<std::vector<SExpr*>>($2)); }
    ;

identifier: symbol
        { $$ = new IdentifierNode {{}, std::unique_ptr<SymbolNode>($1), {}}; }
    | '(' '_' symbol numeral_list ')'
        { $$ = new IdentifierNode {{}, std::unique_ptr<SymbolNode>($3), std::unique_ptr<std::vector<std::unique_ptr<std::string>>>($4)}; }
    ;

sort: identifier
      { $$ = new SortNode {{}, std::unique_ptr<IdentifierNode>($1), std::make_unique<std::vector<SortNode*>>()}; }
    | '(' identifier sort_list sort ')'
      {
        $3->push_back($4);
        $$ = new SortNode {{}, std::unique_ptr<IdentifierNode>($2), std::unique_ptr<std::vector<SortNode*>>($3)};
      }
    ;

sort_list: sort_list sort
        { $1->emplace_back($2); $$ = $1; }
    |
        { $$ = new std::vector<SortNode*>(); }
    ;

s_expr: spec_const
        { $$ = new SExpr{{}, std::unique_ptr<SpecConstNode>($1)}; }
    | symbol
        { $$ = new SExpr{{}, std::unique_ptr<SymbolNode>($1)}; }
    | TK_KEY
        { $$ = new SExpr{{}, std::unique_ptr<std::string>($1)}; }
    | '(' s_expr_list ')'
        { $$ = new SExpr{{}, std::unique_ptr<std::vector<SExpr*>>($2)}; }
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
        { $$ = new SpecConstNode{{}, ConstType::numeral, std::unique_ptr<std::string>($1)}; }
    | TK_DEC
        { $$ = new SpecConstNode{{}, ConstType::decimal, std::unique_ptr<std::string>($1)}; }
    | TK_HEX
        { $$ = new SpecConstNode{{}, ConstType::hexadecimal, std::unique_ptr<std::string>($1)}; }
    | TK_BIN
        { $$ = new SpecConstNode{{}, ConstType::binary, std::unique_ptr<std::string>($1)}; }
    | TK_STR
        { $$ = new SpecConstNode{{}, ConstType::string, std::unique_ptr<std::string>($1)}; }
    ;

const_val: symbol
        { $$ = $1; }
    | spec_const
        { $$ = new SymbolNode {{}, std::unique_ptr<SpecConstNode>($1), false}; }
    ;

numeral_list: numeral_list TK_NUM
        { $1->emplace_back(std::unique_ptr<std::string>($2)); }
    | TK_NUM
        { $$ = new std::vector<std::unique_ptr<std::string>>(); $$->emplace_back(std::unique_ptr<std::string>{$1});  }
    ;

qual_identifier: identifier
        { $$ = new QualIdentifierNode {{}, std::unique_ptr<IdentifierNode>($1)}; }
    | '(' TK_AS identifier sort ')'
        { $$ = new QualIdentifierNode {{}, std::unique_ptr<IdentifierNode>($3), std::unique_ptr<SortNode>($4)}; }
    ;

var_binding_list: var_binding
        { $$ = new std::vector<std::unique_ptr<VarBindingNode>>; $$->push_back(std::unique_ptr<VarBindingNode>($1)); }
    | var_binding_list var_binding
        { $1->emplace_back(std::unique_ptr<VarBindingNode>($2)); $$ = $1; }
    ;

var_binding: '(' symbol term ')'
        { $$ = new VarBindingNode { {}, std::unique_ptr<SymbolNode>($2), $3 }; }
    ;

sorted_var_list:
        { $$ = new std::vector<std::unique_ptr<SortedVarNode>>(); }
    | sorted_var_list sorted_var
        { $1->emplace_back(std::unique_ptr<SortedVarNode>($2)); $$ = $1; }
    ;

sorted_var: '(' symbol sort ')'
        { $$ = new SortedVarNode {{}, std::unique_ptr<SymbolNode>($2), std::unique_ptr<SortNode>($3)}; }

term_list:
        { $$ = new std::vector<TermNode*>(); }
    | term_list term
        { $1->emplace_back($2); $$ = $1; }
    ;

term: spec_const
        { $$ = new NormalTermNode {{}, std::unique_ptr<SpecConstNode>($1), nullptr}; }
    | qual_identifier
        { $$ = new NormalTermNode {{}, std::unique_ptr<IdentifierNode>($1->identifier.release()), std::unique_ptr<SortNode>($1->returnSort.release())}; delete $1; }
    | '(' qual_identifier term_list term ')'
        {
            $3->push_back($4);
            $$ = new NormalTermNode {{std::unique_ptr<std::vector<TermNode*>>($3)}, std::unique_ptr<IdentifierNode>($2->identifier.release()), std::unique_ptr<SortNode>($2->returnSort.release())};
            delete $2;
        }
    | '(' TK_LET '(' var_binding_list ')' term ')'
        { $$ = new LetTermNode {$6, std::unique_ptr<std::vector<std::unique_ptr<VarBindingNode>>>($4)};   }
    | '(' TK_FORALL '(' sorted_var_list ')' term ')' // todo: AST traversal must ensure that sorted_var_list is non-empty
        { $$ = new ForallNode {$6, std::unique_ptr<std::vector<std::unique_ptr<SortedVarNode>>>($4)}; }
    | '(' TK_EXISTS '(' sorted_var_list ')' term ')' // todo: AST traversal must ensure that sorted_var_list is non-empty
        { $$ = new ExistsNode {$6, std::unique_ptr<std::vector<std::unique_ptr<SortedVarNode>>>($4)}; }
    | '(' '!' term attribute_list ')' // todo: AST traversal must ensure that attribute_list is non-empty
        { $$ = new AnnotationNode {$3, std::unique_ptr<std::vector<std::unique_ptr<AttributeNode>>>($4)}; }
    ;

symbol_list:
        { $$ = new std::vector<std::unique_ptr<SymbolNode>>(); }
    | symbol_list symbol
        { $1->push_back(std::unique_ptr<SymbolNode>($2)); $$ = $1; }
    ;

b_value: symbol
        {
            if (auto const str_p = std::get_if<std::unique_ptr<std::string>>(&($1->name))) {
                if (**str_p == "true") {
                    $$ = true;
                } else if (**str_p == "false") {
                    $$ = false;
                } else {
                    printf("Syntax error: expecting either 'true' or 'false', got '%s'\n", (**str_p).c_str());
                    delete $1;
                    YYERROR;
                }
                delete $1;
            } else {
                auto const * node = std::get_if<std::unique_ptr<SpecConstNode>>(&($1->name));
                assert(node);
                printf("Syntax error: expecting either 'true' or 'false', got '%s'\n", (*(*node)->value).c_str());
                delete $1;
                YYERROR;
            }
        }
    ;

option: KW_PRINTSUCCESS b_value
        { $$ = new OptionNode {OptionNode::OptionType::PrintSuccess, $2}; delete $1; }
    | KW_EXPANDDEFINITIONS b_value
        { $$ = new OptionNode {OptionNode::OptionType::ExpandDefinitions, $2}; delete $1; }
    | KW_INTERACTIVEMODE b_value
        { $$ = new OptionNode {OptionNode::OptionType::InteractiveMode, $2}; delete $1; }
    | KW_PRODUCEPROOFS b_value
        { $$ = new OptionNode {OptionNode::OptionType::ProduceProofs, $2}; delete $1; }
    | KW_PRODUCEUNSATCORES b_value
        { $$ = new OptionNode {OptionNode::OptionType::ProduceUnsatCores, $2}; delete $1; }
    | KW_PRODUCEMODELS b_value
        { $$ = new OptionNode {OptionNode::OptionType::ProduceModels, $2}; delete $1; }
    | KW_PRODUCEASSIGNMENTS b_value
        { $$ = new OptionNode {OptionNode::OptionType::ProduceAssignments, $2}; delete $1;}
    | KW_REGULAROUTPUTCHANNEL TK_STR
        { $$ = new OptionNode {OptionNode::OptionType::RegularOutputChannel, std::unique_ptr<std::string>($2)}; delete $1; }
    | KW_DIAGNOSTICOUTPUTCHANNEL TK_STR
        { $$ = new OptionNode {OptionNode::OptionType::DiagnosticOutputChannel, std::unique_ptr<std::string>($2)}; delete $1;  }
    | KW_RANDOMSEED TK_NUM
        { $$ = new OptionNode {OptionNode::OptionType::RandomSeed, static_cast<uint32_t>(std::stoi(*$2)) }; delete $2; delete $1; }
    | KW_VERBOSITY TK_NUM
        { $$ = new OptionNode {OptionNode::OptionType::Verbosity, static_cast<uint32_t>(std::stoi(*$2)) }; delete $2; delete $1; }
    | attribute
        { $$ = new OptionNode {OptionNode::OptionType::Attribute, std::unique_ptr<AttributeNode>($1) }; }
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

