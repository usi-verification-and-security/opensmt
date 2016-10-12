/* A Bison parser, made by GNU Bison 3.0.2.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2013 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

#ifndef YY_SMT2NEW_SMT_NEWPARSER_HH_INCLUDED
# define YY_SMT2NEW_SMT_NEWPARSER_HH_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int smt2newdebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    TK_AS = 258,
    TK_DECIMAL = 259,
    TK_EXISTS = 260,
    TK_FORALL = 261,
    TK_LET = 262,
    TK_NUMERAL = 263,
    TK_PAR = 264,
    TK_STRING = 265,
    TK_ASSERT = 266,
    TK_CHECKSAT = 267,
    TK_DECLARESORT = 268,
    TK_DECLAREFUN = 269,
    TK_DECLARECONST = 270,
    TK_DEFINESORT = 271,
    TK_DEFINEFUN = 272,
    TK_EXIT = 273,
    TK_GETASSERTIONS = 274,
    TK_GETASSIGNMENT = 275,
    TK_GETINFO = 276,
    TK_GETOPTION = 277,
    TK_GETPROOF = 278,
    TK_GETUNSATCORE = 279,
    TK_GETVALUE = 280,
    TK_POP = 281,
    TK_PUSH = 282,
    TK_SETLOGIC = 283,
    TK_SETINFO = 284,
    TK_SETOPTION = 285,
    TK_THEORY = 286,
    TK_GETITPS = 287,
    TK_WRSTATE = 288,
    TK_RDSTATE = 289,
    TK_SIMPLIFY = 290,
    TK_NUM = 291,
    TK_SYM = 292,
    TK_KEY = 293,
    TK_STR = 294,
    TK_DEC = 295,
    TK_HEX = 296,
    TK_BIN = 297,
    KW_SORTS = 298,
    KW_FUNS = 299,
    KW_SORTSDESCRIPTION = 300,
    KW_FUNSDESCRIPTION = 301,
    KW_DEFINITION = 302,
    KW_NOTES = 303,
    KW_THEORIES = 304,
    KW_LANGUAGE = 305,
    KW_EXTENSIONS = 306,
    KW_VALUES = 307,
    KW_PRINTSUCCESS = 308,
    KW_EXPANDDEFINITIONS = 309,
    KW_INTERACTIVEMODE = 310,
    KW_PRODUCEPROOFS = 311,
    KW_PRODUCEUNSATCORES = 312,
    KW_PRODUCEMODELS = 313,
    KW_PRODUCEASSIGNMENTS = 314,
    KW_REGULAROUTPUTCHANNEL = 315,
    KW_DIAGNOSTICOUTPUTCHANNEL = 316,
    KW_RANDOMSEED = 317,
    KW_VERBOSITY = 318,
    KW_ERRORBEHAVIOR = 319,
    KW_NAME = 320,
    KW_NAMED = 321,
    KW_AUTHORS = 322,
    KW_VERSION = 323,
    KW_STATUS = 324,
    KW_REASONUNKNOWN = 325,
    KW_ALLSTATISTICS = 326
  };
#endif
/* Tokens.  */
#define TK_AS 258
#define TK_DECIMAL 259
#define TK_EXISTS 260
#define TK_FORALL 261
#define TK_LET 262
#define TK_NUMERAL 263
#define TK_PAR 264
#define TK_STRING 265
#define TK_ASSERT 266
#define TK_CHECKSAT 267
#define TK_DECLARESORT 268
#define TK_DECLAREFUN 269
#define TK_DECLARECONST 270
#define TK_DEFINESORT 271
#define TK_DEFINEFUN 272
#define TK_EXIT 273
#define TK_GETASSERTIONS 274
#define TK_GETASSIGNMENT 275
#define TK_GETINFO 276
#define TK_GETOPTION 277
#define TK_GETPROOF 278
#define TK_GETUNSATCORE 279
#define TK_GETVALUE 280
#define TK_POP 281
#define TK_PUSH 282
#define TK_SETLOGIC 283
#define TK_SETINFO 284
#define TK_SETOPTION 285
#define TK_THEORY 286
#define TK_GETITPS 287
#define TK_WRSTATE 288
#define TK_RDSTATE 289
#define TK_SIMPLIFY 290
#define TK_NUM 291
#define TK_SYM 292
#define TK_KEY 293
#define TK_STR 294
#define TK_DEC 295
#define TK_HEX 296
#define TK_BIN 297
#define KW_SORTS 298
#define KW_FUNS 299
#define KW_SORTSDESCRIPTION 300
#define KW_FUNSDESCRIPTION 301
#define KW_DEFINITION 302
#define KW_NOTES 303
#define KW_THEORIES 304
#define KW_LANGUAGE 305
#define KW_EXTENSIONS 306
#define KW_VALUES 307
#define KW_PRINTSUCCESS 308
#define KW_EXPANDDEFINITIONS 309
#define KW_INTERACTIVEMODE 310
#define KW_PRODUCEPROOFS 311
#define KW_PRODUCEUNSATCORES 312
#define KW_PRODUCEMODELS 313
#define KW_PRODUCEASSIGNMENTS 314
#define KW_REGULAROUTPUTCHANNEL 315
#define KW_DIAGNOSTICOUTPUTCHANNEL 316
#define KW_RANDOMSEED 317
#define KW_VERBOSITY 318
#define KW_ERRORBEHAVIOR 319
#define KW_NAME 320
#define KW_NAMED 321
#define KW_AUTHORS 322
#define KW_VERSION 323
#define KW_STATUS 324
#define KW_REASONUNKNOWN 325
#define KW_ALLSTATISTICS 326

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE YYSTYPE;
union YYSTYPE
{
#line 66 "smt2newparser.yy" /* yacc.c:1909  */

  char  *                      str;
  std::vector< std::string > * str_list;
  ASTNode *                    snode;
  std::list< ASTNode * > *     snode_list;
  smt2token                    tok;

#line 204 "smt2newparser.hh" /* yacc.c:1909  */
};
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif

/* Location type.  */
#if ! defined YYLTYPE && ! defined YYLTYPE_IS_DECLARED
typedef struct YYLTYPE YYLTYPE;
struct YYLTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
};
# define YYLTYPE_IS_DECLARED 1
# define YYLTYPE_IS_TRIVIAL 1
#endif



int smt2newparse (Smt2newContext* context);

#endif /* !YY_SMT2NEW_SMT_NEWPARSER_HH_INCLUDED  */
