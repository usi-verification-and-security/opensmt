%pure-parser
%name-prefix="smt2new"
%locations
%defines
%error-verbose
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
#include "smt2newparser.h"


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
  char  *                   str;
  std::vector< std::string > *        str_list;
  ASTNode *                 snode;
  std::list< ASTNode * > *       snode_list;
}


%token TK_AS TK_DECIMAL TK_EXISTS TK_FORALL TK_LET TK_NUMERAL TK_PAR TK_STRING
%token TK_ASSERT TK_CHECKSAT TK_DECLARESORT TK_DECLAREFUN TK_DEFINESORT TK_DEFINEFUN TK_EXIT TK_GETASSERTIONS TK_GETASSIGNMENT TK_GETINFO TK_GETOPTION TK_GETPROOF TK_GETUNSATCORE TK_GETVALUE TK_POP TK_PUSH TK_SETLOGIC TK_SETINFO TK_SETOPTION TK_THEORY
%token TK_NUM TK_SYM TK_KEY TK_STR TK_DEC TK_HEX TK_BIN
%token KW_SORTS KW_FUNS KW_SORTSDESCRIPTION KW_FUNSDESCRIPTION KW_DEFINITION KW_NOTES KW_THEORIES KW_LANGUAGE KW_EXTENSIONS KW_VALUES KW_PRINTSUCCESS KW_EXPANDDEFINITIONS KW_INTERACTIVEMODE KW_PRODUCEPROOFS KW_PRODUCEUNSATCORES KW_PRODUCEMODELS KW_PRODUCEASSIGNMENTS KW_REGULAROUTPUTCHANNEL KW_DIAGNOSTICOUTPUTCHANNEL KW_RANDOMSEED KW_VERBOSITY KW_ERRORBEHAVIOR KW_NAME KW_AUTHORS KW_VERSION KW_STATUS KW_REASONUNKNOWN KW_ALLSTATISTICS

%type <str>TK_AS TK_DECIMAL TK_EXISTS TK_FORALL TK_LET TK_NUMERAL TK_PAR TK_STRING
%type <str> TK_ASSERT TK_CHECKSAT TK_DECLARESORT TK_DECLAREFUN TK_DEFINESORT TK_DEFINEFUN TK_EXIT TK_GETASSERTIONS TK_GETASSIGNMENT TK_GETINFO TK_GETOPTION TK_GETPROOF TK_GETUNSATCORE TK_GETVALUE TK_POP TK_PUSH TK_SETLOGIC TK_SETINFO TK_SETOPTION
%type <str> TK_NUM TK_SYM TK_KEY TK_STR TK_DEC TK_HEX TK_BIN meta_spec_const
%type <str> KW_SORTS KW_FUNS KW_SORTSDESCRIPTION KW_FUNSDESCRIPTION KW_DEFINITION KW_NOTES KW_THEORIES KW_LANGUAGE KW_EXTENSIONS KW_VALUES KW_PRINTSUCCESS KW_EXPANDDEFINITIONS KW_INTERACTIVEMODE KW_PRODUCEPROOFS KW_PRODUCEUNSATCORES KW_PRODUCEMODELS KW_PRODUCEASSIGNMENTS KW_REGULAROUTPUTCHANNEL KW_DIAGNOSTICOUTPUTCHANNEL KW_RANDOMSEED KW_VERBOSITY KW_ERRORBEHAVIOR KW_NAME KW_AUTHORS KW_VERSION KW_STATUS KW_REASONUNKNOWN KW_ALLSTATISTICS predef_key
%type <snode> identifier sort command attribute attribute_value s_expr spec_const qual_identifier var_binding sorted_var term
%type <snode_list> sort_list command_list s_expr_list numeral_list term_list var_binding_list attribute_list sorted_var_list symbol_list
%type <snode> sort_symbol_decl fun_symbol_decl par_fun_symbol_decl
%type <snode_list> sort_symbol_decl_list par_fun_symbol_decl_list
%type <snode> theory_attribute theory_decl logic_attribute logic
%type <snode_list> theory_attribute_list logic_attribute_list
%type <snode> b_value option info_flag

%start script

%%

script: command_list { ASTNode *n = new ASTNode(CMDL_T, "main-script"); n->children = $1; context->insertRoot(n); };


command_list:
        { $$ = new std::list<ASTNode*>(); }
    | command_list command
        { (*$1).push_back($2); $$ = $1; }
    ;

command: '(' TK_SETLOGIC TK_SYM ')'
        {
            $$ = new ASTNode(CMD_T, $2);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(SYM_T, $3));
        }
    | '(' TK_SETOPTION option ')'
        {
            $$ = new ASTNode(CMD_T, $2);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($3);
        }
    | '(' TK_SETINFO attribute ')'
        {
            $$ = new ASTNode(CMD_T, $2);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($3);
        }
    | '(' TK_DECLARESORT TK_SYM TK_NUM ')'
        {
            $$ = new ASTNode(CMD_T, $2);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(SYM_T, $3));
            $$->children->push_back(new ASTNode(NUM_T, $4));
        }
    | '(' TK_DEFINESORT TK_SYM '(' symbol_list ')' sort ')'
        {
            $$ = new ASTNode(CMD_T, $2);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(SYM_T, $3));

            ASTNode* syml = new ASTNode(SYML_T, NULL);
            syml->children = $5;
            $$->children->push_back(syml);

            $$->children->push_back($7);
        }

    | '(' TK_DECLAREFUN TK_SYM '(' sort_list ')' sort ')'
        {
            $$ = new ASTNode(CMD_T, $2);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(SYM_T, $3));

            ASTNode* sortl = new ASTNode(SORTL_T, NULL);
            sortl->children = $5;
            $$->children->push_back(sortl);

            $$->children->push_back($7);
        }
    | '(' TK_DEFINEFUN TK_SYM '(' sorted_var_list ')' sort term ')'
        {
            $$ = new ASTNode(CMD_T, $2);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(SYM_T, $3));

            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = $5;
            $$->children->push_back(svl);

            $$->children->push_back($7);
            $$->children->push_back($8);
        }
    | '(' TK_PUSH TK_NUM ')'
        {
            $$ = new ASTNode(CMD_T, $2);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(NUM_T, $3));
        }
    | '(' TK_POP TK_NUM ')'
        {
            $$ = new ASTNode(CMD_T, $2);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(NUM_T, $3));
        }
    | '(' TK_ASSERT term ')'
        {
            $$ = new ASTNode(CMD_T, $2);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($3);
        }
    | '(' TK_CHECKSAT ')'
        {
            $$ = new ASTNode(CMD_T, $2);
        }
    | '(' TK_GETASSERTIONS ')'
        {
            $$ = new ASTNode(CMD_T, $2);
        }
    | '(' TK_GETPROOF ')'
        {
            $$ = new ASTNode(CMD_T, $2);
        }
    | '(' TK_GETUNSATCORE ')'
        {
            $$ = new ASTNode(CMD_T, $2);
        }
    | '(' TK_GETVALUE '(' term term_list ')' ')'
        {
            $$ = new ASTNode(CMD_T, $2);
            $$->children = $5;
            $$->children->push_front($4);
        }
    | '(' TK_GETASSIGNMENT ')'
        {
            $$ = new ASTNode(CMD_T, $2);
        }
    | '(' TK_GETOPTION TK_KEY ')'
        {
            $$ = new ASTNode(CMD_T, $2);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(UATTR_T, $3));
        }
    | '(' TK_GETOPTION predef_key ')'
        {
            $$ = new ASTNode(CMD_T, $2);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(PATTR_T, $3));
        }
    | '(' TK_GETINFO info_flag ')'
        {
            $$ = new ASTNode(CMD_T, $2);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($3);
        }
    | '(' TK_EXIT ')'
        { $$ = new ASTNode(CMD_T, $2); }
    ;

attribute_list:
        { $$ = new std::list<ASTNode*>(); }
    | attribute_list attribute
        { $1->push_back($2); $$ = $1; }
    ;

attribute: TK_KEY
        { $$ = new ASTNode(UATTR_T, $1); }
    | TK_KEY attribute_value
        { $$ = new ASTNode(UATTR_T, $1); $$->children = new std::list<ASTNode*>(); $$->children->push_back($2); }
    | predef_key
        { $$ = new ASTNode(PATTR_T, $1); }
    | predef_key attribute_value
        { $$ = new ASTNode(PATTR_T, $1); $$->children = new std::list<ASTNode*>(); $$->children->push_back($2); }
    ;

attribute_value: spec_const
        { $$ = new ASTNode(SPECC_T, NULL); $$->children = new std::list<ASTNode*>(); $$->children->push_back($1); }
    | TK_SYM
        {
            $$ = new ASTNode(SYM_T, $1);
        }
    | '(' s_expr_list ')'
        {
            $$ = new ASTNode(SEXPRL_T, NULL);
            $$->children = $2;
        }
    ;

identifier: TK_SYM
        { $$ = new ASTNode(SYM_T, $1); }
    | '(' '_' TK_SYM numeral_list ')'
        { $$ = new ASTNode(SYM_T, $3); $$->children = $4; }
    ;

sort: identifier
      { $$ = new ASTNode(ID_T, NULL); $$->children = new std::list<ASTNode*>(); $$->children->push_back($1); }
    | '(' identifier sort sort_list ')'
      {
        $$ = new ASTNode(LID_T, NULL);
        $$->children = $4;
        $$->children->push_front($3);
      }
    ;

sort_list: sort_list sort
        { $1->push_back($2); $$ = $1; }
    |
        { $$ = new std::list<ASTNode*>(); }
    ;

s_expr: spec_const
        {
            $$ = new ASTNode(SPECC_T, NULL);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($1);
        }
    | TK_SYM
        {
            $$ = new ASTNode(SYM_T, $1);
        }
    | TK_KEY
        {
            $$ = new ASTNode(UATTR_T, $1);
        }
    | '(' s_expr_list ')'
        {
            $$ = new ASTNode(SEXPRL_T, NULL);
            $$->children = $2;
        }
    ;

s_expr_list:
        {
            $$ = new std::list<ASTNode*>();
        }
    | s_expr_list s_expr
        {
            $1->push_back($2);
            $$ = $1;
        }
    ;

spec_const: TK_NUM
        { $$ = new ASTNode(NUM_T, $1); }
    | TK_DEC
        { $$ = new ASTNode(DEC_T, $1); }
    | TK_HEX
        { $$ = new ASTNode(HEX_T, $1); }
    | TK_BIN
        { $$ = new ASTNode(BIN_T, $1); }
    | TK_STR
        { $$ = new ASTNode(STR_T, $1); }
    ;

numeral_list: numeral_list TK_NUM
        { $1->push_back(new ASTNode(NUM_T, $2)); $$ = $1; }
    | TK_NUM
        { $$ = new std::list<ASTNode*>(); $$->push_back(new ASTNode(NUM_T, $1)); }
    ;

qual_identifier: identifier
        { $$ = $1; }
    | '(' TK_AS identifier sort ')'
        {
            $$ = new ASTNode(AS_T, NULL);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($3);
            $$->children->push_back($4);
        }
    ;

var_binding_list:
        { $$ = new std::list<ASTNode*>(); }
    | var_binding_list var_binding
        { $1->push_back($2); $$ = $1; }
    ;

var_binding: '(' TK_SYM term ')'
        { $$ = new ASTNode(VARB_T, $2); $$->children = new std::list<ASTNode*>(); $$->children->push_back($3); }
    ;

sorted_var_list:
        { $$ = new std::list<ASTNode*>(); }
    | sorted_var_list sorted_var
        { $1->push_back($2); $$ = $1; }
    ;

sorted_var: '(' TK_SYM sort ')'
        { $$ = new ASTNode(SV_T, $2);  $$->children = new std::list<ASTNode*>(); $$->children->push_back($3); }

term_list:
        { $$ = new std::list<ASTNode*>(); }
    | term_list term
        { $1->push_back($2); $$ = $1; }
    ;

term: spec_const
        { $$ = new ASTNode(TERM_T, NULL); $$->children = new std::list<ASTNode*>(); $$->children->push_back($1); }
    | qual_identifier
        { $$ = new ASTNode(QID_T, NULL); $$->children = new std::list<ASTNode*>(); $$->children->push_back($1); }
    | '(' qual_identifier term term_list ')'
        {
            $$ = new ASTNode(LQID_T, NULL);
            $$->children = $4;
            $$->children->push_front($3);
            $$->children->push_front($2);
        }
    | '(' TK_LET '(' var_binding var_binding_list ')' term ')'
        {
            $$ = new ASTNode(LET_T, NULL);
            $$->children = new std::list<ASTNode*>();
            $5->push_front($4);
            ASTNode* vbl = new ASTNode(VARBL_T, NULL);
            vbl->children = $5;
            $$->children->push_back(vbl);
            $$->children->push_back($7);
        }
    | '(' TK_FORALL '(' sorted_var sorted_var_list ')' term ')'
        {
            $$ = new ASTNode(FORALL_T, NULL);
            $$->children = new std::list<ASTNode*>();
            $5->push_front($4);
            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = $5;
            $$->children->push_back(svl);
            $$->children->push_back($7);
        }
    | '(' TK_EXISTS '(' sorted_var sorted_var_list ')' term ')'
        {
            $$ = new ASTNode(EXISTS_T, NULL);
            $$->children = new std::list<ASTNode*>();
            $5->push_front($4);
            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = $5;
            $$->children->push_back(svl);
            $$->children->push_back($7);
        }
    | '!' term attribute attribute_list
        {
            $$ = new ASTNode(BANG_T, NULL);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($2);
            $4->push_front($3);
            $$->children = $4;
        }
    ;


sort_symbol_decl_list:
        { $$ = new list<ASTNode*>(); }
    | sort_symbol_decl_list sort_symbol_decl
        { $1->push_back($2); $$ = $1; }
    ;

sort_symbol_decl: '(' identifier TK_NUM attribute_list ')'
        {
            $$ = new ASTNode(SSYMD_T, NULL);
            $$->children = $4;
            $$->children->push_front(new ASTNode(NUM_T, $3));
            $$->children->push_front($2);
        }
    ;

meta_spec_const: TK_NUM
        { $$ = new ASTNode(NUM_T, $1); }
    | TK_DEC
        { $$ = new ASTNode(DEC_T, $1); }
    | TK_STR
        { $$ = new ASTNode(STR_T, $1); }
    ;

fun_symbol_decl:'(' spec_const sort attribute_list ')'
        {
            $$ = new ASTNode(FSYMD_T, NULL);
            $$->children = new std::list<ASTNode*>();

            $$->children->push_back($2);
            $$->children->push_back($3);
            ASTNode* al = new ASTNode(GATTRL_T, NULL);
            al->children = $4;
            $$->children->push_back(al);
        }
    | '(' meta_spec_const sort attribute_list ')'
        {
            $$ = new ASTNode(FSYMD_T, NULL);
            $$->children = new std::list<ASTNode*>();

            $$->children->push_back($2);
            $$->children->push_back($3);
            ASTNode* al = new ASTNode(GATTRL_T, NULL);
            al->children = $4;
            $$->children->push_back(al);
        }
    | '(' identifier sort sort_list attribute_list ')'
        {
            $$ = new ASTNode(FSYMD_T, NULL);
            $$->children = new std::list<ASTNode*>();

            $$->children->push_back($2);

            ASTNode* sl = new ASTNode(SORTL_T, NULL);
            sl->children = $4;
            sl->children->push_front($3);
            $$->children->push_back(sl);

            ASTNode* al = new ASTNode(GATTRL_T, NULL);
            al->children = $4;
            $$->children->push_back(al);
        }
    ;

symbol_list:
        { $$ = new std::list<ASTNode*>(); }
    | symbol_list TK_SYM
        { $1->push_back(new ASTNode(SYM_T, $2)); $$ = $1; }
    ;

par_fun_symbol_decl_list:
        { $$ = new list<ASTNode*>(); }
    | par_fun_symbol_decl_list par_fun_symbol_decl
        { $1->push_back($2); $$ = $1; }
    ;

par_fun_symbol_decl: fun_symbol_decl
        {
            $$ = new ASTNode(PFSYMD_T, NULL);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($1);
        }
    | '(' TK_PAR '(' TK_SYM symbol_list ')' '(' identifier sort sort_list attribute_list ')' ')'
        {
            $$ = new ASTNode(PFSYMD_T, NULL);
            ASTNode* syml = new ASTNode(SYML_T, NULL);
            $$->children = new std::list<ASTNode*>();

            syml->children = $5;
            syml->children->push_front($4);
            $$->children->push_back(syml);

            ASTNode* id = new ASTNode(PFID_T, NULL)
            id->children = new std::list<ASTNode*>();

            id->children->push_back($8);

            ASTNode* sortl = new ASTNode(SORTL_T, NULL);
            sortl->children = $10;
            sortl->push_front($9);

            id->children->push_back(sortl);

            ASTNode* attrl = new ASTNode(GATTRL_T, NULL);
            attrl->children = $11;
            id->children->push_back(attrl);

            $$->children->push_back(id);
        }
    ;

theory_attribute_list:
        { $$ = new std::list<ASTNode*>(); }
    | theory_attribute_list theory_attribute
        { $1->push_back($2); $$ = $1; }
    ;

theory_attribute: KW_SORTS '(' sort_symbol_decl sort_symbol_decl_list ')'
        {
            $$ = new ASTNode(TATTR_T, $1);
            $4->push_front($3);
            $$->children = $4;
        }
    | KW_FUNS '(' par_fun_symbol_decl par_fun_symbol_decl_list ')'
        {
            $$ = new ASTNode(TATTR_T, $1);
            $4->push_front($3);
            $$->children = $4;
        }
    | KW_SORTSDESCRIPTION TK_STR
        {
            $$ = new ASTNode(TATTR_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(STR_T, $1));
        }
    | KW_FUNSDESCRIPTION TK_STR
        {
            $$ = new ASTNode(TATTR_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(STR_T, $1));
        }
    | KW_DEFINITION TK_STR
        {
            $$ = new ASTNode(TATTR_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(STR_T, $1));
        }
    | KW_VALUES TK_STR
        {
            $$ = new ASTNode(TATTR_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(STR_T, $1));
        }
    | KW_NOTES TK_STR
        {
            $$ = new ASTNode(TATTR_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(STR_T, $1));
        }
    | attribute
        {
            $$ = new ASTNode(TATTR_T, NULL);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($1);
        }
    ;

theory_decl: '(' TK_THEORY TK_SYM theory_attribute theory_attribute_list ')'
        {
            $$ = new ASTNode(TDECL_T, $3);
            $$->children = $5;
            $$->children->push_back($4);
        }
    ;

logic_attribute_list:
        { $$ = new std::list<ASTNode*>(); }
    | logic_attribute_list logic_attribute
        { $1->push_back($2); $$ = $1; }
    ;

logic_attribute: KW_THEORIES '(' TK_SYM symbol_list ')'
        {
            $$ = new ASTNode(LATTR_T, $1);
            $4->push_front(new ASTNode(SYM_T, $3));
            $$->children = $4;
        }
    | KW_LANGUAGE TK_STR
        {
            $$ = new ASTNode(LATTR_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(STR_T, $2));
        }
    | KW_EXTENSIONS TK_STR
        {
            $$ = new ASTNode(LATTR_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(STR_T, $2));
        }
    | KW_VALUES TK_STR
        {
            $$ = new ASTNode(LATTR_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(STR_T, $2));
        }
    | KW_NOTES TK_STR
        {
            $$ = new ASTNode(LATTR_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(STR_T, $2));
        }
    | attribute
        { $$ = new ASTNode(LATTR_T, $1); }
    ;

logic: '(' TK_SYM logic_attribute logic_attribute_list ')'
        {
            $$ = new ASTNode(LOGIC_T, $2);
            $$->children = $4;
            $$->push_front($3);
        }
    ;

b_value: TK_SYM
        {
            if (strcmp($1, "true") == 0)
                $$ = new ASTNode(BOOL_T, "true");
            else if (strcmp($1, "false") == 0)
                $$ = new ASTNode(BOOL_T, "false");
            else {
                printf("Syntax error: expecting either 'true' or 'false', got '%s'\n", $1);
                YYERROR;
            }
        }
    ;

option: KW_PRINTSUCCESS b_value
        {
            $$ = new ASTNode(OPTION_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($2);
        }
    | KW_EXPANDDEFINITIONS b_value
        {
            $$ = new ASTNode(OPTION_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($2);
        }
    | KW_INTERACTIVEMODE b_value
        {
            $$ = new ASTNode(OPTION_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($2);
        }
    | KW_PRODUCEPROOFS b_value
        {
            $$ = new ASTNode(OPTION_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($2);
        }
    | KW_PRODUCEUNSATCORES b_value
        {
            $$ = new ASTNode(OPTION_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($2);
        }
    | KW_PRODUCEMODELS b_value
        {
            $$ = new ASTNode(OPTION_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($2);
        }
    | KW_PRODUCEASSIGNMENTS b_value
        {
            $$ = new ASTNode(OPTION_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($2);
        }
    | KW_REGULAROUTPUTCHANNEL TK_STR
        {
            $$ = new ASTNode(OPTION_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(STR_T, $2));
        }
    | KW_DIAGNOSTICOUTPUTCHANNEL TK_STR
        {
            $$ = new ASTNode(OPTION_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(STR_T, $2));
        }
    | KW_RANDOMSEED TK_NUM
        {
            $$ = new ASTNode(OPTION_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(NUM_T, $2));
        }
    | KW_VERBOSITY TK_NUM
        {
            $$ = new ASTNode(OPTION_T, $1);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(NUM_T, $2));
        }
    | attribute
        {
            $$ = new ASTNode(OPTION_T, NULL);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back($1);
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
    | KW_LANGUAGE
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
        { $$ = new ASTNode(INFO_T, $1); }
    | KW_NAME
        { $$ = new ASTNode(INFO_T, $1); }
    | KW_AUTHORS
        { $$ = new ASTNode(INFO_T, $1); }
    | KW_VERSION
        { $$ = new ASTNode(INFO_T, $1); }
    | KW_STATUS
        { $$ = new ASTNode(INFO_T, $1); }
    | KW_REASONUNKNOWN
        { $$ = new ASTNode(INFO_T, $1); }
    | KW_ALLSTATISTICS
        { $$ = new ASTNode(INFO_T, $1); }
    | TK_KEY
        {
            $$ = new ASTNode(INFO_T, NULL);
            $$->children = new std::list<ASTNode*>();
            $$->children->push_back(new ASTNode(GATTR_T, $1));
        }
    ;

%%

//=======================================================================================
// Auxiliary Routines

