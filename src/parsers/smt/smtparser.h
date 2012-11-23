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
     TK_STR = 259,
     TK_BVNUM = 260,
     TK_BVNUM_NO_WIDTH = 261,
     TK_BIT0 = 262,
     TK_BIT1 = 263,
     TK_REAL = 264,
     TK_INT = 265,
     TK_BITVEC = 266,
     TK_U = 267,
     TK_ARRAY = 268,
     TK_ARRAY_INDEX = 269,
     TK_ARRAY_ELEMENT = 270,
     TK_PLUS = 271,
     TK_MINUS = 272,
     TK_TIMES = 273,
     TK_UMINUS = 274,
     TK_DIV = 275,
     TK_NE = 276,
     TK_EQ = 277,
     TK_LEQ = 278,
     TK_GEQ = 279,
     TK_LT = 280,
     TK_GT = 281,
     TK_AND = 282,
     TK_OR = 283,
     TK_NOT = 284,
     TK_IFF = 285,
     TK_XOR = 286,
     TK_ITE = 287,
     TK_IFTHENELSE = 288,
     TK_IMPLIES = 289,
     TK_BENCHMARK = 290,
     TK_SOURCE = 291,
     TK_ARGUMENT = 292,
     TK_STATUS = 293,
     TK_NOTES = 294,
     TK_EXTRASORTS = 295,
     TK_EXTRAPREDS = 296,
     TK_EXTRAFUNS = 297,
     TK_LOGIC = 298,
     TK_CATEGORY = 299,
     TK_DIFFICULTY = 300,
     TK_ASSUMPTION = 301,
     TK_FORMULA = 302,
     TK_TRUE = 303,
     TK_FALSE = 304,
     TK_INTERPOLATE = 305,
     TK_FLET = 306,
     TK_FLET_STR = 307,
     TK_LET = 308,
     TK_LET_STR = 309,
     TK_DISTINCT = 310,
     TK_BVSLT = 311,
     TK_BVSGT = 312,
     TK_BVSLE = 313,
     TK_BVSGE = 314,
     TK_BVULT = 315,
     TK_BVUGT = 316,
     TK_BVULE = 317,
     TK_BVUGE = 318,
     TK_EXTRACT = 319,
     TK_CONCAT = 320,
     TK_BVAND = 321,
     TK_BVOR = 322,
     TK_BVXOR = 323,
     TK_BVNOT = 324,
     TK_BVADD = 325,
     TK_BVNEG = 326,
     TK_BVMUL = 327,
     TK_BVASHR = 328,
     TK_REPEAT = 329,
     TK_SIGN_EXTEND = 330,
     TK_ZERO_EXTEND = 331,
     TK_ROTATE_LEFT = 332,
     TK_ROTATE_RIGHT = 333,
     TK_BVLSHR = 334,
     TK_BVSHL = 335,
     TK_BVSREM = 336,
     TK_BVSDIV = 337,
     TK_BVSUB = 338,
     TK_BVUDIV = 339,
     TK_BVUREM = 340,
     TK_ARRAY_SELECT = 341,
     TK_ARRAY_STORE = 342
   };
#endif
/* Tokens.  */
#define TK_NUM 258
#define TK_STR 259
#define TK_BVNUM 260
#define TK_BVNUM_NO_WIDTH 261
#define TK_BIT0 262
#define TK_BIT1 263
#define TK_REAL 264
#define TK_INT 265
#define TK_BITVEC 266
#define TK_U 267
#define TK_ARRAY 268
#define TK_ARRAY_INDEX 269
#define TK_ARRAY_ELEMENT 270
#define TK_PLUS 271
#define TK_MINUS 272
#define TK_TIMES 273
#define TK_UMINUS 274
#define TK_DIV 275
#define TK_NE 276
#define TK_EQ 277
#define TK_LEQ 278
#define TK_GEQ 279
#define TK_LT 280
#define TK_GT 281
#define TK_AND 282
#define TK_OR 283
#define TK_NOT 284
#define TK_IFF 285
#define TK_XOR 286
#define TK_ITE 287
#define TK_IFTHENELSE 288
#define TK_IMPLIES 289
#define TK_BENCHMARK 290
#define TK_SOURCE 291
#define TK_ARGUMENT 292
#define TK_STATUS 293
#define TK_NOTES 294
#define TK_EXTRASORTS 295
#define TK_EXTRAPREDS 296
#define TK_EXTRAFUNS 297
#define TK_LOGIC 298
#define TK_CATEGORY 299
#define TK_DIFFICULTY 300
#define TK_ASSUMPTION 301
#define TK_FORMULA 302
#define TK_TRUE 303
#define TK_FALSE 304
#define TK_INTERPOLATE 305
#define TK_FLET 306
#define TK_FLET_STR 307
#define TK_LET 308
#define TK_LET_STR 309
#define TK_DISTINCT 310
#define TK_BVSLT 311
#define TK_BVSGT 312
#define TK_BVSLE 313
#define TK_BVSGE 314
#define TK_BVULT 315
#define TK_BVUGT 316
#define TK_BVULE 317
#define TK_BVUGE 318
#define TK_EXTRACT 319
#define TK_CONCAT 320
#define TK_BVAND 321
#define TK_BVOR 322
#define TK_BVXOR 323
#define TK_BVNOT 324
#define TK_BVADD 325
#define TK_BVNEG 326
#define TK_BVMUL 327
#define TK_BVASHR 328
#define TK_REPEAT 329
#define TK_SIGN_EXTEND 330
#define TK_ZERO_EXTEND 331
#define TK_ROTATE_LEFT 332
#define TK_ROTATE_RIGHT 333
#define TK_BVLSHR 334
#define TK_BVSHL 335
#define TK_BVSREM 336
#define TK_BVSDIV 337
#define TK_BVSUB 338
#define TK_BVUDIV 339
#define TK_BVUREM 340
#define TK_ARRAY_SELECT 341
#define TK_ARRAY_STORE 342




#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
#line 53 "smtparser.yy"
{
  char  *              str;
  Enode *              enode;
  vector< unsigned > * type_list;
}
/* Line 1529 of yacc.c.  */
#line 229 "smtparser.h"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif

extern YYSTYPE smtlval;

