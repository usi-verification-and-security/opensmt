/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015 Free Software Foundation, Inc.

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

#ifndef YY_SMT2NEW_SMT2NEW_SMT2NEWPARSER_HH_INCLUDED
# define YY_SMT2NEW_SMT2NEW_SMT2NEWPARSER_HH_INCLUDED
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
    TK_WRFUNS = 291,
    TK_NUM = 292,
    TK_SYM = 293,
    TK_KEY = 294,
    TK_STR = 295,
    TK_DEC = 296,
    TK_HEX = 297,
    TK_BIN = 298,
    KW_SORTS = 299,
    KW_FUNS = 300,
    KW_SORTSDESCRIPTION = 301,
    KW_FUNSDESCRIPTION = 302,
    KW_DEFINITION = 303,
    KW_NOTES = 304,
    KW_THEORIES = 305,
    KW_LANGUAGE = 306,
    KW_EXTENSIONS = 307,
    KW_VALUES = 308,
    KW_PRINTSUCCESS = 309,
    KW_EXPANDDEFINITIONS = 310,
    KW_INTERACTIVEMODE = 311,
    KW_PRODUCEPROOFS = 312,
    KW_PRODUCEUNSATCORES = 313,
    KW_PRODUCEMODELS = 314,
    KW_PRODUCEASSIGNMENTS = 315,
    KW_REGULAROUTPUTCHANNEL = 316,
    KW_DIAGNOSTICOUTPUTCHANNEL = 317,
    KW_RANDOMSEED = 318,
    KW_VERBOSITY = 319,
    KW_ERRORBEHAVIOR = 320,
    KW_NAME = 321,
    KW_NAMED = 322,
    KW_AUTHORS = 323,
    KW_VERSION = 324,
    KW_STATUS = 325,
    KW_REASONUNKNOWN = 326,
    KW_ALLSTATISTICS = 327
  };
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED

union YYSTYPE
{
#line 66 "smt2new/smt2newparser.yy" /* yacc.c:1909  */

  char  *                      str;
  std::vector< std::string > * str_list;
  ASTNode *                    snode;
  std::list< ASTNode * > *     snode_list;
  smt2token                    tok;

#line 135 "smt2new/smt2newparser.hh" /* yacc.c:1909  */
};

typedef union YYSTYPE YYSTYPE;
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

#endif /* !YY_SMT2NEW_SMT2NEW_SMT2NEWPARSER_HH_INCLUDED  */
