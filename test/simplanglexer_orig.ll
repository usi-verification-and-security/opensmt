%option prefix="simplang"
%option reentrant
%option bison-bridge
%option bison-locations
%option noyywrap
%option yylineno

%{

#include <cstdio>
#include <cstdlib>
#include <vector>
#include <list>

#include "simplangcontext.h"
#include "simplangparser.h"

#define YY_EXTRA_TYPE SimplangContext*
#define YY_USER_ACTION yylloc->first_line = yylineno;

#define YY_INPUT(buf,result,max_size)           \
{                                               \
    char c;                                     \
    (yyextra->is) >> c;                         \
    if (yyextra->is.eof())                      \
        result = YY_NULL;                       \
    else {                                      \
        buf[0] = c;                             \
        result = 1;                             \
    }                                           \
}

%}

%x start_source
%x start_string

%%

"declare-fun"                { yylval->str = strdup( yytext ); printf("f: declare-fun\n"); return TK_DECLAREFUN; }
/*"set-logic"                  { yylval->str = strdup( yytext ); printf("f: set-logic\n"); return TK_SETLOGIC; }
"set-info"                   { yylval->str = strdup( yytext ); printf("f: set-info\n"); return TK_SETINFO; }
[ \t\n]+                     // Eat up whitespace
";".*\n                      { printf("A comment\n"); }*/
/*
\:[a-zA-Z0-9~!@\$\%\^&\*_\-\+=\<\>\.\?\/]+                                     { yylval->str = strdup( yytext ); return TK_KEY; }

0|[1-9][0-9]*                                                                  { yylval->str = strdup( yytext ); return TK_NUM; }
[0-9]+\.0*[0-9]+                                                               { yylval->str = strdup( yytext ); return TK_DEC; }
#x[a-fA-F0-9]+                                                                 { yylval->str = strdup( yytext ); return TK_HEX; }
#b[0-1]+                                                                       { yylval->str = strdup( yytext ); return TK_BIN; }
*/
[a-zA-Z~!@\$\%\^&\*\-\+=\<\>\.\?\/'][a-zA-Z0-9~!@\$\%\^&\*_\-\+=\<\>\.\?\/']*|_[a-zA-Z0-9~!@\$\%\^&\*_\-\+=\<\>\.\?\/']+ { yylval->str = strdup( yytext ); return TK_SYM; }

[()]            { return *yytext; }
/*
_               { return *yytext; }

\"              { BEGIN(start_string); printf("Noticed a string\n"); }

<start_string>{
  \"            { yylval->str = strdup(yyextra->getBuf()); yyextra->clearBuf();
                    BEGIN(INITIAL); printf("Noticed an end of a string\n"); return TK_STR; }
  [ ]           { yyextra->insertBuf(' '); printf("Noticed a space\n"); }
  [\t]          { yyextra->insertBuf('\t'); printf("Noticed a tab\n"); }
  \n            { yyextra->insertBuf('\n'); printf("Noticed a newline\n"); }
  "b"           { printf("Noticed a special letter b\n"); }
  \\            { if (yytext[1] == '"') {
                     yyextra->insertBuf('"');
                     printf("Noticed an escaped double quote\n");
                  }
                  else if (yytext[1] == '\\') {
                     yyextra->insertBuf('\\');
                     printf("Noticed an escaped backslash\n");
                  }
                  yytext ++;
                }
  [^\\\n\"b]   { yyextra->insertBuf(yytext[0]); printf("Noticed a character `%c'\n", yytext[0]); }
}

\|              { BEGIN(start_source); }
<start_source>{
  [^\|\n]       { yyextra->insertBuf(yytext[0]); }
  \n            { yyextra->insertBuf('\n'); }
  \|            { yylval->str = strdup(yyextra->getBuf()); yyextra->clearBuf();
                   BEGIN(INITIAL); return TK_SYM; }
}
*/
.               { printf( "Syntax error at line %d near %s\n", yylineno, yytext ); exit( 1 ); }

%%

void SimplangContext::init_scanner()
{
    yylex_init(&scanner);
    yyset_extra(this, scanner);
}

void SimplangContext::destroy_scanner()
{
    yylex_destroy(scanner);
}
