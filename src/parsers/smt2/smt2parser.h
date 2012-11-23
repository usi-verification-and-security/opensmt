/* A Bison parser, made by GNU Bison 2.3.  */

/* Skeleton interface for Bison's Yacc-like parsers in C

   Copyright (C) 1984, 1989, 1990, 2000, 2001, 2002, 2003, 2004, 2005, 2006
   Free Software Foundation, Inc.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2, or (at your option)
   any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor,
   Boston, MA 02110-1301, USA.  */

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
     TK_NUM = 258,
     TK_DEC = 259,
     TK_HEX = 260,
     TK_STR = 261,
     TK_SYM = 262,
     TK_KEY = 263,
     TK_BIN = 264,
     TK_BOOL = 265,
     TK_SETLOGIC = 266,
     TK_SETINFO = 267,
     TK_SETOPTION = 268,
     TK_DECLARESORT = 269,
     TK_DEFINESORT = 270,
     TK_DECLAREFUN = 271,
     TK_PUSH = 272,
     TK_POP = 273,
     TK_CHECKSAT = 274,
     TK_GETASSERTIONS = 275,
     TK_GETPROOF = 276,
     TK_GETUNSATCORE = 277,
     TK_GETINTERPOLANTS = 278,
     TK_GETVALUE = 279,
     TK_GETASSIGNMENT = 280,
     TK_GETOPTION = 281,
     TK_GETINFO = 282,
     TK_EXIT = 283,
     TK_AS = 284,
     TK_LET = 285,
     TK_FORALL = 286,
     TK_EXISTS = 287,
     TK_ANNOT = 288,
     TK_DISTINCT = 289,
     TK_DEFINEFUN = 290,
     TK_ASSERT = 291,
     TK_REAL = 292,
     TK_INT = 293,
     TK_ARRAY = 294,
     TK_PLUS = 295,
     TK_MINUS = 296,
     TK_TIMES = 297,
     TK_UMINUS = 298,
     TK_DIV = 299,
     TK_NE = 300,
     TK_EQ = 301,
     TK_LEQ = 302,
     TK_GEQ = 303,
     TK_LT = 304,
     TK_GT = 305,
     TK_AND = 306,
     TK_OR = 307,
     TK_NOT = 308,
     TK_IFF = 309,
     TK_XOR = 310,
     TK_ITE = 311,
     TK_IFTHENELSE = 312,
     TK_IMPLIES = 313,
     TK_TRUE = 314,
     TK_FALSE = 315,
     TK_INTERPOLATE = 316,
     TK_BVSLT = 317,
     TK_BVSGT = 318,
     TK_BVSLE = 319,
     TK_BVSGE = 320,
     TK_BVULT = 321,
     TK_BVUGT = 322,
     TK_BVULE = 323,
     TK_BVUGE = 324,
     TK_EXTRACT = 325,
     TK_CONCAT = 326,
     TK_BVAND = 327,
     TK_BVOR = 328,
     TK_BVXOR = 329,
     TK_BVNOT = 330,
     TK_BVADD = 331,
     TK_BVNEG = 332,
     TK_BVMUL = 333,
     TK_BVASHR = 334,
     TK_REPEAT = 335,
     TK_SIGN_EXTEND = 336,
     TK_ZERO_EXTEND = 337,
     TK_ROTATE_LEFT = 338,
     TK_ROTATE_RIGHT = 339,
     TK_BVLSHR = 340,
     TK_BVSHL = 341,
     TK_BVSREM = 342,
     TK_BVSDIV = 343,
     TK_BVSUB = 344,
     TK_BVUDIV = 345,
     TK_BVUREM = 346,
     TK_PRINT_SUCCESS = 347,
     TK_EXPAND_DEFINITIONS = 348,
     TK_INTERACTIVE_MODE = 349,
     TK_PRODUCE_PROOFS = 350,
     TK_PRODUCE_UNSAT_CORES = 351,
     TK_PRODUCE_INTERPOLANTS = 352,
     TK_PRODUCE_MODELS = 353,
     TK_PRODUCE_ASSIGNMENTS = 354,
     TK_REGULAR_OUTPUT_CHANNEL = 355,
     TK_DIAGNOSTIC_OUTPUT_CHANNEL = 356,
     TK_RANDOM_SEED = 357,
     TK_VERBOSITY = 358,
     TK_STORE = 359,
     TK_SELECT = 360,
     TK_DIFF = 361
   };
#endif
/* Tokens.  */
#define TK_NUM 258
#define TK_DEC 259
#define TK_HEX 260
#define TK_STR 261
#define TK_SYM 262
#define TK_KEY 263
#define TK_BIN 264
#define TK_BOOL 265
#define TK_SETLOGIC 266
#define TK_SETINFO 267
#define TK_SETOPTION 268
#define TK_DECLARESORT 269
#define TK_DEFINESORT 270
#define TK_DECLAREFUN 271
#define TK_PUSH 272
#define TK_POP 273
#define TK_CHECKSAT 274
#define TK_GETASSERTIONS 275
#define TK_GETPROOF 276
#define TK_GETUNSATCORE 277
#define TK_GETINTERPOLANTS 278
#define TK_GETVALUE 279
#define TK_GETASSIGNMENT 280
#define TK_GETOPTION 281
#define TK_GETINFO 282
#define TK_EXIT 283
#define TK_AS 284
#define TK_LET 285
#define TK_FORALL 286
#define TK_EXISTS 287
#define TK_ANNOT 288
#define TK_DISTINCT 289
#define TK_DEFINEFUN 290
#define TK_ASSERT 291
#define TK_REAL 292
#define TK_INT 293
#define TK_ARRAY 294
#define TK_PLUS 295
#define TK_MINUS 296
#define TK_TIMES 297
#define TK_UMINUS 298
#define TK_DIV 299
#define TK_NE 300
#define TK_EQ 301
#define TK_LEQ 302
#define TK_GEQ 303
#define TK_LT 304
#define TK_GT 305
#define TK_AND 306
#define TK_OR 307
#define TK_NOT 308
#define TK_IFF 309
#define TK_XOR 310
#define TK_ITE 311
#define TK_IFTHENELSE 312
#define TK_IMPLIES 313
#define TK_TRUE 314
#define TK_FALSE 315
#define TK_INTERPOLATE 316
#define TK_BVSLT 317
#define TK_BVSGT 318
#define TK_BVSLE 319
#define TK_BVSGE 320
#define TK_BVULT 321
#define TK_BVUGT 322
#define TK_BVULE 323
#define TK_BVUGE 324
#define TK_EXTRACT 325
#define TK_CONCAT 326
#define TK_BVAND 327
#define TK_BVOR 328
#define TK_BVXOR 329
#define TK_BVNOT 330
#define TK_BVADD 331
#define TK_BVNEG 332
#define TK_BVMUL 333
#define TK_BVASHR 334
#define TK_REPEAT 335
#define TK_SIGN_EXTEND 336
#define TK_ZERO_EXTEND 337
#define TK_ROTATE_LEFT 338
#define TK_ROTATE_RIGHT 339
#define TK_BVLSHR 340
#define TK_BVSHL 341
#define TK_BVSREM 342
#define TK_BVSDIV 343
#define TK_BVSUB 344
#define TK_BVUDIV 345
#define TK_BVUREM 346
#define TK_PRINT_SUCCESS 347
#define TK_EXPAND_DEFINITIONS 348
#define TK_INTERACTIVE_MODE 349
#define TK_PRODUCE_PROOFS 350
#define TK_PRODUCE_UNSAT_CORES 351
#define TK_PRODUCE_INTERPOLANTS 352
#define TK_PRODUCE_MODELS 353
#define TK_PRODUCE_ASSIGNMENTS 354
#define TK_REGULAR_OUTPUT_CHANNEL 355
#define TK_DIAGNOSTIC_OUTPUT_CHANNEL 356
#define TK_RANDOM_SEED 357
#define TK_VERBOSITY 358
#define TK_STORE 359
#define TK_SELECT 360
#define TK_DIFF 361




#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
#line 60 "smt2parser.yy"
{
  char  *                   str;
  vector< string > *        str_list;
  Enode *                   enode;
  Snode *                   snode;
  list< Snode * > *         snode_list;
  map< Enode *, Enode * > * binding_list;
  Anode *                   anode;
  list< Anode * > *         anode_list;
  SpNode *                  spnode;
  IdNode *                  idnode;
}
/* Line 1529 of yacc.c.  */
#line 274 "smt2parser.h"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif

extern YYSTYPE smt2lval;

