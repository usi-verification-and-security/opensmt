/* A Bison parser, made by GNU Bison 2.5.  */

/* Bison interface for Yacc-like parsers in C
   
      Copyright (C) 1984, 1989-1990, 2000-2011 Free Software Foundation, Inc.
   
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


/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
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
     TK_DEFINESORT = 270,
     TK_DEFINEFUN = 271,
     TK_EXIT = 272,
     TK_GETASSERTIONS = 273,
     TK_GETASSIGNMENT = 274,
     TK_GETINFO = 275,
     TK_GETOPTION = 276,
     TK_GETPROOF = 277,
     TK_GETUNSATCORE = 278,
     TK_GETVALUE = 279,
     TK_POP = 280,
     TK_PUSH = 281,
     TK_SETLOGIC = 282,
     TK_SETINFO = 283,
     TK_SETOPTION = 284,
     TK_THEORY = 285,
     TK_GETITPS = 286,
     TK_DUMPSTATE = 287,
     TK_NUM = 288,
     TK_SYM = 289,
     TK_KEY = 290,
     TK_STR = 291,
     TK_DEC = 292,
     TK_HEX = 293,
     TK_BIN = 294,
     KW_SORTS = 295,
     KW_FUNS = 296,
     KW_SORTSDESCRIPTION = 297,
     KW_FUNSDESCRIPTION = 298,
     KW_DEFINITION = 299,
     KW_NOTES = 300,
     KW_THEORIES = 301,
     KW_LANGUAGE = 302,
     KW_EXTENSIONS = 303,
     KW_VALUES = 304,
     KW_PRINTSUCCESS = 305,
     KW_EXPANDDEFINITIONS = 306,
     KW_INTERACTIVEMODE = 307,
     KW_PRODUCEPROOFS = 308,
     KW_PRODUCEUNSATCORES = 309,
     KW_PRODUCEMODELS = 310,
     KW_PRODUCEASSIGNMENTS = 311,
     KW_REGULAROUTPUTCHANNEL = 312,
     KW_DIAGNOSTICOUTPUTCHANNEL = 313,
     KW_RANDOMSEED = 314,
     KW_VERBOSITY = 315,
     KW_ERRORBEHAVIOR = 316,
     KW_NAME = 317,
     KW_NAMED = 318,
     KW_AUTHORS = 319,
     KW_VERSION = 320,
     KW_STATUS = 321,
     KW_REASONUNKNOWN = 322,
     KW_ALLSTATISTICS = 323
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
#define TK_DEFINESORT 270
#define TK_DEFINEFUN 271
#define TK_EXIT 272
#define TK_GETASSERTIONS 273
#define TK_GETASSIGNMENT 274
#define TK_GETINFO 275
#define TK_GETOPTION 276
#define TK_GETPROOF 277
#define TK_GETUNSATCORE 278
#define TK_GETVALUE 279
#define TK_POP 280
#define TK_PUSH 281
#define TK_SETLOGIC 282
#define TK_SETINFO 283
#define TK_SETOPTION 284
#define TK_THEORY 285
#define TK_GETITPS 286
#define TK_DUMPSTATE 287
#define TK_NUM 288
#define TK_SYM 289
#define TK_KEY 290
#define TK_STR 291
#define TK_DEC 292
#define TK_HEX 293
#define TK_BIN 294
#define KW_SORTS 295
#define KW_FUNS 296
#define KW_SORTSDESCRIPTION 297
#define KW_FUNSDESCRIPTION 298
#define KW_DEFINITION 299
#define KW_NOTES 300
#define KW_THEORIES 301
#define KW_LANGUAGE 302
#define KW_EXTENSIONS 303
#define KW_VALUES 304
#define KW_PRINTSUCCESS 305
#define KW_EXPANDDEFINITIONS 306
#define KW_INTERACTIVEMODE 307
#define KW_PRODUCEPROOFS 308
#define KW_PRODUCEUNSATCORES 309
#define KW_PRODUCEMODELS 310
#define KW_PRODUCEASSIGNMENTS 311
#define KW_REGULAROUTPUTCHANNEL 312
#define KW_DIAGNOSTICOUTPUTCHANNEL 313
#define KW_RANDOMSEED 314
#define KW_VERBOSITY 315
#define KW_ERRORBEHAVIOR 316
#define KW_NAME 317
#define KW_NAMED 318
#define KW_AUTHORS 319
#define KW_VERSION 320
#define KW_STATUS 321
#define KW_REASONUNKNOWN 322
#define KW_ALLSTATISTICS 323




#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
{

/* Line 2068 of yacc.c  */
#line 66 "smt2newparser.yy"

  char  *                      str;
  std::vector< std::string > * str_list;
  ASTNode *                    snode;
  std::list< ASTNode * > *     snode_list;



/* Line 2068 of yacc.c  */
#line 195 "smt2newparser.h"
} YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
#endif



#if ! defined YYLTYPE && ! defined YYLTYPE_IS_DECLARED
typedef struct YYLTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
} YYLTYPE;
# define yyltype YYLTYPE /* obsolescent; will be withdrawn */
# define YYLTYPE_IS_DECLARED 1
# define YYLTYPE_IS_TRIVIAL 1
#endif



