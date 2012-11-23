/* A Bison parser, made by GNU Bison 2.3.  */

/* Skeleton implementation for Bison's Yacc-like parsers in C

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "2.3"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Using locations.  */
#define YYLSP_NEEDED 0

/* Substitute the variable and function names.  */
#define yyparse smtparse
#define yylex   smtlex
#define yyerror smterror
#define yylval  smtlval
#define yychar  smtchar
#define yydebug smtdebug
#define yynerrs smtnerrs


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




/* Copy the first part of user declarations.  */
#line 20 "smtparser.yy"


#include "Global.h"

#include "Egraph.h"
#include "ANode.h"
#include "OpenSMTContext.h"
#include <cstdio>
#include <cstdlib>
#include <cassert>

extern int smtlineno;
extern int smtlex( );
extern OpenSMTContext * parser_ctx;

vector< unsigned > * createTypeList  ( unsigned );
vector< unsigned > * createTypeList  ( unsigned, const char * );
vector< unsigned > * pushTypeList    ( vector< unsigned > *, unsigned );
vector< unsigned > * pushTypeList    ( vector< unsigned > *, unsigned, const char * );
void		     destroyTypeList ( vector< unsigned > * );

void smterror( const char * s )
{
  printf( "%d: %s \n", smtlineno, s );
  exit( 1 );
}

/* Overallocation to prevent stack overflow */
#define YYMAXDEPTH 1024 * 1024



/* Enabling traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 1
#endif

/* Enabling the token table.  */
#ifndef YYTOKEN_TABLE
# define YYTOKEN_TABLE 0
#endif

#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
#line 53 "smtparser.yy"
{
  char  *              str;
  Enode *              enode;
  vector< unsigned > * type_list;
}
/* Line 193 of yacc.c.  */
#line 316 "smtparser.cc"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif



/* Copy the second part of user declarations.  */


/* Line 216 of yacc.c.  */
#line 329 "smtparser.cc"

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#elif (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
typedef signed char yytype_int8;
#else
typedef short int yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(e) ((void) (e))
#else
# define YYUSE(e) /* empty */
#endif

/* Identity function, used to suppress warnings about constant conditions.  */
#ifndef lint
# define YYID(n) (n)
#else
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static int
YYID (int i)
#else
static int
YYID (i)
    int i;
#endif
{
  return i;
}
#endif

#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#     ifndef _STDLIB_H
#      define _STDLIB_H 1
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (YYID (0))
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined _STDLIB_H \
       && ! ((defined YYMALLOC || defined malloc) \
	     && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef _STDLIB_H
#    define _STDLIB_H 1
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
	 || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss;
  YYSTYPE yyvs;
  };

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

/* Copy COUNT objects from FROM to TO.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(To, From, Count) \
      __builtin_memcpy (To, From, (Count) * sizeof (*(From)))
#  else
#   define YYCOPY(To, From, Count)		\
      do					\
	{					\
	  YYSIZE_T yyi;				\
	  for (yyi = 0; yyi < (Count); yyi++)	\
	    (To)[yyi] = (From)[yyi];		\
	}					\
      while (YYID (0))
#  endif
# endif

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack)					\
    do									\
      {									\
	YYSIZE_T yynewbytes;						\
	YYCOPY (&yyptr->Stack, Stack, yysize);				\
	Stack = &yyptr->Stack;						\
	yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
	yyptr += yynewbytes / sizeof (*yyptr);				\
      }									\
    while (YYID (0))

#endif

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  39
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   232

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  93
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  40
/* YYNRULES -- Number of rules.  */
#define YYNRULES  108
/* YYNRULES -- Number of states.  */
#define YYNSTATES  226

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   342

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
      88,    89,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    92,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    90,     2,    91,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    87
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     7,    10,    13,    16,    19,    22,    24,
      26,    28,    30,    32,    35,    38,    41,    44,    47,    50,
      53,    56,    58,    60,    62,    64,    66,    68,    70,    72,
      75,    78,    81,    84,    87,    90,    93,    96,    99,   102,
     105,   108,   111,   113,   115,   117,   119,   121,   123,   128,
     133,   138,   142,   147,   153,   158,   163,   169,   174,   179,
     188,   196,   198,   200,   202,   207,   212,   217,   223,   228,
     238,   244,   249,   255,   260,   264,   267,   270,   273,   278,
     283,   288,   293,   298,   303,   310,   316,   322,   324,   326,
     329,   331,   336,   341,   346,   351,   353,   355,   357,   362,
     364,   369,   372,   374,   380,   382,   384,   386,   393
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int16 yyrhs[] =
{
      94,     0,    -1,    88,    95,    89,    -1,    95,    96,    -1,
      95,   105,    -1,    95,   122,    -1,    95,   123,    -1,    95,
     124,    -1,    96,    -1,   105,    -1,   122,    -1,   123,    -1,
     124,    -1,    96,    97,    -1,    96,    99,    -1,    96,   100,
      -1,    96,   101,    -1,    96,   102,    -1,    96,   103,    -1,
      96,   104,    -1,    96,    98,    -1,    97,    -1,    99,    -1,
     100,    -1,   101,    -1,   102,    -1,   103,    -1,   104,    -1,
      98,    -1,    35,     4,    -1,    50,     3,    -1,    39,    37,
      -1,    36,    37,    -1,    38,     4,    -1,    44,    37,    -1,
      45,    37,    -1,    43,     4,    -1,   105,   107,    -1,   105,
     109,    -1,   105,   111,    -1,   105,   113,    -1,   105,   115,
      -1,   106,    -1,   107,    -1,   109,    -1,   111,    -1,   113,
      -1,   115,    -1,    40,    88,     4,    89,    -1,    41,    88,
     108,    89,    -1,   108,    88,     4,    89,    -1,    88,     4,
      89,    -1,    42,    88,   110,    89,    -1,   110,    88,     4,
       9,    89,    -1,    88,     4,     9,    89,    -1,    42,    88,
     112,    89,    -1,   112,    88,     4,    10,    89,    -1,    88,
       4,    10,    89,    -1,    42,    88,   114,    89,    -1,   114,
      88,     4,    11,    90,     3,    91,    89,    -1,    88,     4,
      11,    90,     3,    91,    89,    -1,   116,    -1,   117,    -1,
     118,    -1,    42,    88,   119,    89,    -1,    42,    88,   120,
      89,    -1,    42,    88,   121,    89,    -1,   119,    88,     4,
      13,    89,    -1,    88,     4,    13,    89,    -1,    88,     4,
      13,    90,     3,    92,     3,    91,    89,    -1,   120,    88,
       4,    14,    89,    -1,    88,     4,    14,    89,    -1,   121,
      88,     4,    15,    89,    -1,    88,     4,    15,    89,    -1,
     122,    46,   125,    -1,    46,   125,    -1,    47,   125,    -1,
      47,     3,    -1,    88,    27,   126,    89,    -1,    88,    28,
     126,    89,    -1,    88,    34,   126,    89,    -1,    88,    29,
     126,    89,    -1,    88,    30,   126,    89,    -1,    88,    31,
     126,    89,    -1,    88,    33,   125,   125,   125,    89,    -1,
      88,    51,   128,   125,    89,    -1,    88,    53,   127,   125,
      89,    -1,    52,    -1,   129,    -1,   125,   126,    -1,   125,
      -1,    88,    54,   130,    89,    -1,    88,    52,   125,    89,
      -1,    88,    22,   131,    89,    -1,    88,    55,   131,    89,
      -1,     4,    -1,    48,    -1,    49,    -1,    88,     4,   131,
      89,    -1,   132,    -1,    88,     4,   131,    89,    -1,   130,
     131,    -1,   130,    -1,    88,    20,     3,     3,    89,    -1,
       3,    -1,     4,    -1,    54,    -1,    88,    32,   125,   132,
     132,    89,    -1,    88,     4,   131,    89,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,    88,    88,    91,    92,    93,    94,    95,    96,    97,
      98,    99,   100,   103,   104,   105,   106,   107,   108,   109,
     110,   111,   112,   113,   114,   115,   116,   117,   118,   121,
     125,   129,   133,   137,   145,   149,   153,   201,   202,   203,
     204,   207,   208,   209,   210,   211,   212,   215,   218,   226,
     229,   239,   251,   254,   264,   276,   279,   289,   301,   304,
     313,   324,   325,   326,   329,   332,   335,   338,   348,   358,
     370,   378,   387,   395,   484,   486,   490,   494,   502,   504,
     506,   508,   510,   512,   514,   516,   518,   520,   522,   526,
     528,   532,   535,   564,   566,   568,   570,   572,   574,   578,
     588,   592,   594,   606,   610,   612,   614,   616,   618
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "TK_NUM", "TK_STR", "TK_BVNUM",
  "TK_BVNUM_NO_WIDTH", "TK_BIT0", "TK_BIT1", "TK_REAL", "TK_INT",
  "TK_BITVEC", "TK_U", "TK_ARRAY", "TK_ARRAY_INDEX", "TK_ARRAY_ELEMENT",
  "TK_PLUS", "TK_MINUS", "TK_TIMES", "TK_UMINUS", "TK_DIV", "TK_NE",
  "TK_EQ", "TK_LEQ", "TK_GEQ", "TK_LT", "TK_GT", "TK_AND", "TK_OR",
  "TK_NOT", "TK_IFF", "TK_XOR", "TK_ITE", "TK_IFTHENELSE", "TK_IMPLIES",
  "TK_BENCHMARK", "TK_SOURCE", "TK_ARGUMENT", "TK_STATUS", "TK_NOTES",
  "TK_EXTRASORTS", "TK_EXTRAPREDS", "TK_EXTRAFUNS", "TK_LOGIC",
  "TK_CATEGORY", "TK_DIFFICULTY", "TK_ASSUMPTION", "TK_FORMULA", "TK_TRUE",
  "TK_FALSE", "TK_INTERPOLATE", "TK_FLET", "TK_FLET_STR", "TK_LET",
  "TK_LET_STR", "TK_DISTINCT", "TK_BVSLT", "TK_BVSGT", "TK_BVSLE",
  "TK_BVSGE", "TK_BVULT", "TK_BVUGT", "TK_BVULE", "TK_BVUGE", "TK_EXTRACT",
  "TK_CONCAT", "TK_BVAND", "TK_BVOR", "TK_BVXOR", "TK_BVNOT", "TK_BVADD",
  "TK_BVNEG", "TK_BVMUL", "TK_BVASHR", "TK_REPEAT", "TK_SIGN_EXTEND",
  "TK_ZERO_EXTEND", "TK_ROTATE_LEFT", "TK_ROTATE_RIGHT", "TK_BVLSHR",
  "TK_BVSHL", "TK_BVSREM", "TK_BVSDIV", "TK_BVSUB", "TK_BVUDIV",
  "TK_BVUREM", "TK_ARRAY_SELECT", "TK_ARRAY_STORE", "'('", "')'", "'['",
  "']'", "':'", "$accept", "top", "all", "header_declaration",
  "benchmark_declaration", "interpolation_declaration",
  "notes_declaration", "source_declaration", "status_declaration",
  "category_declaration", "difficulty_declaration", "logic_declaration",
  "variables_declaration", "sort_declaration", "bool_variable_declaration",
  "bool_variable_list", "real_variable_declaration", "real_variable_list",
  "int_variable_declaration", "int_variable_list",
  "bitvec_variable_declaration", "bitvec_variable_list",
  "arrayrelated_variable_declaration", "array_variable_declaration",
  "array_index_variable_declaration", "array_element_variable_declaration",
  "array_variable_list", "array_index_variable_list",
  "array_element_variable_list", "assumption_declaration",
  "formula_declaration", "formula_n_declaration", "formula",
  "formula_list", "let_def", "flet_def", "atom", "expression",
  "expression_list", "arithmetic_expression", 0
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311,   312,   313,   314,
     315,   316,   317,   318,   319,   320,   321,   322,   323,   324,
     325,   326,   327,   328,   329,   330,   331,   332,   333,   334,
     335,   336,   337,   338,   339,   340,   341,   342,    40,    41,
      91,    93,    58
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    93,    94,    95,    95,    95,    95,    95,    95,    95,
      95,    95,    95,    96,    96,    96,    96,    96,    96,    96,
      96,    96,    96,    96,    96,    96,    96,    96,    96,    97,
      98,    99,   100,   101,   102,   103,   104,   105,   105,   105,
     105,   105,   105,   105,   105,   105,   105,   105,   106,   107,
     108,   108,   109,   110,   110,   111,   112,   112,   113,   114,
     114,   115,   115,   115,   116,   117,   118,   119,   119,   119,
     120,   120,   121,   121,   122,   122,   123,   124,   125,   125,
     125,   125,   125,   125,   125,   125,   125,   125,   125,   126,
     126,   127,   128,   129,   129,   129,   129,   129,   129,   130,
     130,   131,   131,   132,   132,   132,   132,   132,   132
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     3,     2,     2,     2,     2,     2,     1,     1,
       1,     1,     1,     2,     2,     2,     2,     2,     2,     2,
       2,     1,     1,     1,     1,     1,     1,     1,     1,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     1,     1,     1,     1,     1,     1,     4,     4,
       4,     3,     4,     5,     4,     4,     5,     4,     4,     8,
       7,     1,     1,     1,     4,     4,     4,     5,     4,     9,
       5,     4,     5,     4,     3,     2,     2,     2,     4,     4,
       4,     4,     4,     4,     6,     5,     5,     1,     1,     2,
       1,     4,     4,     4,     4,     1,     1,     1,     4,     1,
       4,     2,     1,     5,     1,     1,     1,     6,     4
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     8,    21,    28,
      22,    23,    24,    25,    26,    27,     9,    42,    43,    44,
      45,    46,    47,    61,    62,    63,    10,    11,    12,     1,
      29,    32,    33,    31,     0,     0,     0,    36,    34,    35,
      95,    96,    97,    87,     0,    75,    88,    77,    76,    30,
       2,     3,     4,     5,     6,     7,    13,    20,    14,    15,
      16,    17,    18,    19,    37,    38,    39,    40,    41,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    74,    48,     0,     0,    49,     0,     0,    52,
       0,    55,     0,    58,     0,    64,     0,    65,     0,    66,
     104,   105,   106,     0,   102,     0,    99,     0,    90,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    51,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   101,    98,
      93,    89,    78,    79,    81,    82,    83,     0,    80,     0,
       0,     0,     0,    94,    50,    54,    57,     0,    68,     0,
      71,    73,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    85,     0,    86,     0,     0,    53,    56,
       0,    67,    70,    72,   100,     0,     0,     0,    84,    92,
      91,     0,     0,     0,   103,     0,     0,    60,     0,     0,
       0,   107,     0,    59,   108,    69
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,    16,    17,    18,    19,    20,    21,    22,    23,
      24,    25,    26,    27,    28,    82,    29,    84,    30,    85,
      31,    86,    32,    33,    34,    35,    87,    88,    89,    36,
      37,    38,   128,   129,   139,   137,    56,   124,   125,   126
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -161
static const yytype_int16 yypact[] =
{
     -55,    93,    37,    44,    27,    82,    53,     9,    24,    42,
      91,    62,    73,     6,     1,   111,   -24,   114,  -161,  -161,
    -161,  -161,  -161,  -161,  -161,  -161,   -10,  -161,  -161,  -161,
    -161,  -161,  -161,  -161,  -161,  -161,    72,  -161,  -161,  -161,
    -161,  -161,  -161,  -161,   121,    54,    57,  -161,  -161,  -161,
    -161,  -161,  -161,  -161,    47,  -161,  -161,  -161,  -161,  -161,
    -161,   114,   -10,    72,  -161,  -161,  -161,  -161,  -161,  -161,
    -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,     6,
      58,   142,   -48,   144,   -46,   -44,   -26,    16,    28,    31,
       3,     3,     6,     6,     6,     6,     6,     6,     6,    63,
      67,     3,  -161,  -161,    71,   164,  -161,   152,   165,  -161,
     166,  -161,   167,  -161,   168,  -161,   169,  -161,   170,  -161,
    -161,  -161,  -161,    81,     3,    86,  -161,    87,     6,    88,
      89,    90,    92,    94,     6,    95,   128,     6,   131,     6,
      97,  -161,    98,    99,   100,   101,    33,   103,   104,   173,
     180,   183,   182,   184,   181,     3,   194,     6,  -161,  -161,
    -161,  -161,  -161,  -161,  -161,  -161,  -161,     6,  -161,     6,
     110,     3,   112,  -161,  -161,  -161,  -161,   197,  -161,   199,
    -161,  -161,   115,   116,   113,   117,   118,   119,   120,   207,
       5,   122,   123,  -161,   124,  -161,   125,   126,  -161,  -161,
     211,  -161,  -161,  -161,  -161,   130,    83,     5,  -161,  -161,
    -161,   132,   212,   129,  -161,     3,   133,  -161,   134,   135,
     137,  -161,   138,  -161,  -161,  -161
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -161,  -161,  -161,   201,   -15,     7,    10,    11,    12,    18,
      21,    22,   213,  -161,    -1,  -161,     8,  -161,    26,  -161,
      30,  -161,    34,  -161,  -161,  -161,  -161,  -161,  -161,   214,
     215,   216,   -13,    13,  -161,  -161,  -161,    52,   -88,  -160
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -1
static const yytype_uint8 yytable[] =
{
      55,    58,    66,   127,    57,    50,   120,   121,   120,   121,
      50,     3,     4,   140,     5,     6,     7,     8,     9,    10,
      11,    12,    13,    14,    67,    74,    15,    68,    69,    70,
     207,     8,     9,     1,    75,    71,   158,    39,    72,    73,
     105,   106,   108,   109,   110,   111,    66,   216,    40,    51,
      52,    90,    76,    53,    51,    52,    77,   122,    53,   122,
      78,    74,   112,   113,    41,    60,   102,   188,    67,    91,
      75,    68,    69,    70,    92,    93,    94,    95,    96,    71,
      97,    98,    72,    73,   134,   155,    42,   215,    76,    54,
      43,   123,    77,   206,    54,    47,    78,    44,    99,    48,
     100,   156,   101,   156,   114,   115,   130,   131,   132,   133,
      49,   135,    45,   157,    59,   157,   116,   117,    79,   118,
     119,   167,   178,   179,   170,    80,   172,   220,     3,     4,
      46,     5,     6,     7,     8,     9,    10,    11,    12,    13,
      14,   161,    81,    15,   190,    83,   104,   103,   107,     3,
       4,   136,     5,     6,   191,   138,   192,    10,    11,    12,
     141,   143,   144,   145,    15,   146,   147,   148,   142,   149,
     150,   151,   152,   153,   154,   159,   160,   162,   163,   164,
     169,   165,   182,   166,   168,   171,   173,   174,   175,   176,
     183,   177,   180,   181,   184,   185,   187,   189,   186,   193,
     196,   195,   197,   200,   198,   199,   201,   202,   203,   204,
     205,   208,   209,   210,   213,   218,   211,    61,   212,   214,
     219,   217,   221,   194,   223,   222,   224,   225,     0,    62,
      63,    64,    65
};

static const yytype_int16 yycheck[] =
{
      13,    14,    17,    91,     3,     4,     3,     4,     3,     4,
       4,    35,    36,   101,    38,    39,    40,    41,    42,    43,
      44,    45,    46,    47,    17,    26,    50,    17,    17,    17,
     190,    41,    42,    88,    26,    17,   124,     0,    17,    17,
      88,    89,    88,    89,    88,    89,    61,   207,     4,    48,
      49,     4,    26,    52,    48,    49,    26,    54,    52,    54,
      26,    62,    88,    89,    37,    89,    79,   155,    61,    22,
      62,    61,    61,    61,    27,    28,    29,    30,    31,    61,
      33,    34,    61,    61,    97,     4,     4,     4,    62,    88,
      37,    88,    62,    88,    88,     4,    62,    88,    51,    37,
      53,    20,    55,    20,    88,    89,    93,    94,    95,    96,
      37,    98,    88,    32,     3,    32,    88,    89,    46,    88,
      89,   134,    89,    90,   137,     4,   139,   215,    35,    36,
      88,    38,    39,    40,    41,    42,    43,    44,    45,    46,
      47,   128,    88,    50,   157,    88,     4,    89,     4,    35,
      36,    88,    38,    39,   167,    88,   169,    43,    44,    45,
      89,     9,    10,    11,    50,    13,    14,    15,     4,     4,
       4,     4,     4,     4,     4,    89,    89,    89,    89,    89,
      52,    89,     9,    89,    89,    54,    89,    89,    89,    89,
      10,    90,    89,    89,    11,    13,    15,     3,    14,    89,
       3,    89,     3,    90,    89,    89,    89,    89,    89,    89,
       3,    89,    89,    89,     3,     3,    91,    16,    92,    89,
      91,    89,    89,   171,    89,    91,    89,    89,    -1,    16,
      16,    16,    16
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    88,    94,    35,    36,    38,    39,    40,    41,    42,
      43,    44,    45,    46,    47,    50,    95,    96,    97,    98,
      99,   100,   101,   102,   103,   104,   105,   106,   107,   109,
     111,   113,   115,   116,   117,   118,   122,   123,   124,     0,
       4,    37,     4,    37,    88,    88,    88,     4,    37,    37,
       4,    48,    49,    52,    88,   125,   129,     3,   125,     3,
      89,    96,   105,   122,   123,   124,    97,    98,    99,   100,
     101,   102,   103,   104,   107,   109,   111,   113,   115,    46,
       4,    88,   108,    88,   110,   112,   114,   119,   120,   121,
       4,    22,    27,    28,    29,    30,    31,    33,    34,    51,
      53,    55,   125,    89,     4,    88,    89,     4,    88,    89,
      88,    89,    88,    89,    88,    89,    88,    89,    88,    89,
       3,     4,    54,    88,   130,   131,   132,   131,   125,   126,
     126,   126,   126,   126,   125,   126,    88,   128,    88,   127,
     131,    89,     4,     9,    10,    11,    13,    14,    15,     4,
       4,     4,     4,     4,     4,     4,    20,    32,   131,    89,
      89,   126,    89,    89,    89,    89,    89,   125,    89,    52,
     125,    54,   125,    89,    89,    89,    89,    90,    89,    90,
      89,    89,     9,    10,    11,    13,    14,    15,   131,     3,
     125,   125,   125,    89,   130,    89,     3,     3,    89,    89,
      90,    89,    89,    89,    89,     3,    88,   132,    89,    89,
      89,    91,    92,     3,    89,     4,   132,    89,     3,    91,
     131,    89,    91,    89,    89,    89
};

#define yyerrok		(yyerrstatus = 0)
#define yyclearin	(yychar = YYEMPTY)
#define YYEMPTY		(-2)
#define YYEOF		0

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrorlab


/* Like YYERROR except do call yyerror.  This remains here temporarily
   to ease the transition to the new meaning of YYERROR, for GCC.
   Once GCC version 2 has supplanted version 1, this can go.  */

#define YYFAIL		goto yyerrlab

#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)					\
do								\
  if (yychar == YYEMPTY && yylen == 1)				\
    {								\
      yychar = (Token);						\
      yylval = (Value);						\
      yytoken = YYTRANSLATE (yychar);				\
      YYPOPSTACK (1);						\
      goto yybackup;						\
    }								\
  else								\
    {								\
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;							\
    }								\
while (YYID (0))


#define YYTERROR	1
#define YYERRCODE	256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#define YYRHSLOC(Rhs, K) ((Rhs)[K])
#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)				\
    do									\
      if (YYID (N))                                                    \
	{								\
	  (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;	\
	  (Current).first_column = YYRHSLOC (Rhs, 1).first_column;	\
	  (Current).last_line    = YYRHSLOC (Rhs, N).last_line;		\
	  (Current).last_column  = YYRHSLOC (Rhs, N).last_column;	\
	}								\
      else								\
	{								\
	  (Current).first_line   = (Current).last_line   =		\
	    YYRHSLOC (Rhs, 0).last_line;				\
	  (Current).first_column = (Current).last_column =		\
	    YYRHSLOC (Rhs, 0).last_column;				\
	}								\
    while (YYID (0))
#endif


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL
#  define YY_LOCATION_PRINT(File, Loc)			\
     fprintf (File, "%d.%d-%d.%d",			\
	      (Loc).first_line, (Loc).first_column,	\
	      (Loc).last_line,  (Loc).last_column)
# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


/* YYLEX -- calling `yylex' with the right arguments.  */

#ifdef YYLEX_PARAM
# define YYLEX yylex (YYLEX_PARAM)
#else
# define YYLEX yylex ()
#endif

/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)			\
do {						\
  if (yydebug)					\
    YYFPRINTF Args;				\
} while (YYID (0))

# define YY_SYMBOL_PRINT(Title, Type, Value, Location)			  \
do {									  \
  if (yydebug)								  \
    {									  \
      YYFPRINTF (stderr, "%s ", Title);					  \
      yy_symbol_print (stderr,						  \
		  Type, Value); \
      YYFPRINTF (stderr, "\n");						  \
    }									  \
} while (YYID (0))


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_value_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# else
  YYUSE (yyoutput);
# endif
  switch (yytype)
    {
      default:
	break;
    }
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (yytype < YYNTOKENS)
    YYFPRINTF (yyoutput, "token %s (", yytname[yytype]);
  else
    YYFPRINTF (yyoutput, "nterm %s (", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_stack_print (yytype_int16 *bottom, yytype_int16 *top)
#else
static void
yy_stack_print (bottom, top)
    yytype_int16 *bottom;
    yytype_int16 *top;
#endif
{
  YYFPRINTF (stderr, "Stack now");
  for (; bottom <= top; ++bottom)
    YYFPRINTF (stderr, " %d", *bottom);
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)				\
do {								\
  if (yydebug)							\
    yy_stack_print ((Bottom), (Top));				\
} while (YYID (0))


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_reduce_print (YYSTYPE *yyvsp, int yyrule)
#else
static void
yy_reduce_print (yyvsp, yyrule)
    YYSTYPE *yyvsp;
    int yyrule;
#endif
{
  int yynrhs = yyr2[yyrule];
  int yyi;
  unsigned long int yylno = yyrline[yyrule];
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
	     yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      fprintf (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr, yyrhs[yyprhs[yyrule] + yyi],
		       &(yyvsp[(yyi + 1) - (yynrhs)])
		       		       );
      fprintf (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (yydebug)				\
    yy_reduce_print (yyvsp, Rule); \
} while (YYID (0))

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif



#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static YYSIZE_T
yystrlen (const char *yystr)
#else
static YYSIZE_T
yystrlen (yystr)
    const char *yystr;
#endif
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static char *
yystpcpy (char *yydest, const char *yysrc)
#else
static char *
yystpcpy (yydest, yysrc)
    char *yydest;
    const char *yysrc;
#endif
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
	switch (*++yyp)
	  {
	  case '\'':
	  case ',':
	    goto do_not_strip_quotes;

	  case '\\':
	    if (*++yyp != '\\')
	      goto do_not_strip_quotes;
	    /* Fall through.  */
	  default:
	    if (yyres)
	      yyres[yyn] = *yyp;
	    yyn++;
	    break;

	  case '"':
	    if (yyres)
	      yyres[yyn] = '\0';
	    return yyn;
	  }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into YYRESULT an error message about the unexpected token
   YYCHAR while in state YYSTATE.  Return the number of bytes copied,
   including the terminating null byte.  If YYRESULT is null, do not
   copy anything; just return the number of bytes that would be
   copied.  As a special case, return 0 if an ordinary "syntax error"
   message will do.  Return YYSIZE_MAXIMUM if overflow occurs during
   size calculation.  */
static YYSIZE_T
yysyntax_error (char *yyresult, int yystate, int yychar)
{
  int yyn = yypact[yystate];

  if (! (YYPACT_NINF < yyn && yyn <= YYLAST))
    return 0;
  else
    {
      int yytype = YYTRANSLATE (yychar);
      YYSIZE_T yysize0 = yytnamerr (0, yytname[yytype]);
      YYSIZE_T yysize = yysize0;
      YYSIZE_T yysize1;
      int yysize_overflow = 0;
      enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
      char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
      int yyx;

# if 0
      /* This is so xgettext sees the translatable formats that are
	 constructed on the fly.  */
      YY_("syntax error, unexpected %s");
      YY_("syntax error, unexpected %s, expecting %s");
      YY_("syntax error, unexpected %s, expecting %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s");
# endif
      char *yyfmt;
      char const *yyf;
      static char const yyunexpected[] = "syntax error, unexpected %s";
      static char const yyexpecting[] = ", expecting %s";
      static char const yyor[] = " or %s";
      char yyformat[sizeof yyunexpected
		    + sizeof yyexpecting - 1
		    + ((YYERROR_VERBOSE_ARGS_MAXIMUM - 2)
		       * (sizeof yyor - 1))];
      char const *yyprefix = yyexpecting;

      /* Start YYX at -YYN if negative to avoid negative indexes in
	 YYCHECK.  */
      int yyxbegin = yyn < 0 ? -yyn : 0;

      /* Stay within bounds of both yycheck and yytname.  */
      int yychecklim = YYLAST - yyn + 1;
      int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
      int yycount = 1;

      yyarg[0] = yytname[yytype];
      yyfmt = yystpcpy (yyformat, yyunexpected);

      for (yyx = yyxbegin; yyx < yyxend; ++yyx)
	if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR)
	  {
	    if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
	      {
		yycount = 1;
		yysize = yysize0;
		yyformat[sizeof yyunexpected - 1] = '\0';
		break;
	      }
	    yyarg[yycount++] = yytname[yyx];
	    yysize1 = yysize + yytnamerr (0, yytname[yyx]);
	    yysize_overflow |= (yysize1 < yysize);
	    yysize = yysize1;
	    yyfmt = yystpcpy (yyfmt, yyprefix);
	    yyprefix = yyor;
	  }

      yyf = YY_(yyformat);
      yysize1 = yysize + yystrlen (yyf);
      yysize_overflow |= (yysize1 < yysize);
      yysize = yysize1;

      if (yysize_overflow)
	return YYSIZE_MAXIMUM;

      if (yyresult)
	{
	  /* Avoid sprintf, as that infringes on the user's name space.
	     Don't have undefined behavior even if the translation
	     produced a string with the wrong number of "%s"s.  */
	  char *yyp = yyresult;
	  int yyi = 0;
	  while ((*yyp = *yyf) != '\0')
	    {
	      if (*yyp == '%' && yyf[1] == 's' && yyi < yycount)
		{
		  yyp += yytnamerr (yyp, yyarg[yyi++]);
		  yyf += 2;
		}
	      else
		{
		  yyp++;
		  yyf++;
		}
	    }
	}
      return yysize;
    }
}
#endif /* YYERROR_VERBOSE */


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
#else
static void
yydestruct (yymsg, yytype, yyvaluep)
    const char *yymsg;
    int yytype;
    YYSTYPE *yyvaluep;
#endif
{
  YYUSE (yyvaluep);

  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  switch (yytype)
    {

      default:
	break;
    }
}


/* Prevent warnings from -Wmissing-prototypes.  */

#ifdef YYPARSE_PARAM
#if defined __STDC__ || defined __cplusplus
int yyparse (void *YYPARSE_PARAM);
#else
int yyparse ();
#endif
#else /* ! YYPARSE_PARAM */
#if defined __STDC__ || defined __cplusplus
int yyparse (void);
#else
int yyparse ();
#endif
#endif /* ! YYPARSE_PARAM */



/* The look-ahead symbol.  */
int yychar;

/* The semantic value of the look-ahead symbol.  */
YYSTYPE yylval;

/* Number of syntax errors so far.  */
int yynerrs;



/*----------.
| yyparse.  |
`----------*/

#ifdef YYPARSE_PARAM
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void *YYPARSE_PARAM)
#else
int
yyparse (YYPARSE_PARAM)
    void *YYPARSE_PARAM;
#endif
#else /* ! YYPARSE_PARAM */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void)
#else
int
yyparse ()

#endif
#endif
{
  
  int yystate;
  int yyn;
  int yyresult;
  /* Number of tokens to shift before error messages enabled.  */
  int yyerrstatus;
  /* Look-ahead token as an internal (translated) token number.  */
  int yytoken = 0;
#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

  /* Three stacks and their tools:
     `yyss': related to states,
     `yyvs': related to semantic values,
     `yyls': related to locations.

     Refer to the stacks thru separate pointers, to allow yyoverflow
     to reallocate them elsewhere.  */

  /* The state stack.  */
  yytype_int16 yyssa[YYINITDEPTH];
  yytype_int16 *yyss = yyssa;
  yytype_int16 *yyssp;

  /* The semantic value stack.  */
  YYSTYPE yyvsa[YYINITDEPTH];
  YYSTYPE *yyvs = yyvsa;
  YYSTYPE *yyvsp;



#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  YYSIZE_T yystacksize = YYINITDEPTH;

  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;


  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY;		/* Cause a token to be read.  */

  /* Initialize stack pointers.
     Waste one element of value and location stack
     so that they stay on the same level as the state stack.
     The wasted elements are never initialized.  */

  yyssp = yyss;
  yyvsp = yyvs;

  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
	/* Give user a chance to reallocate the stack.  Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	YYSTYPE *yyvs1 = yyvs;
	yytype_int16 *yyss1 = yyss;


	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if yyoverflow is a macro.  */
	yyoverflow (YY_("memory exhausted"),
		    &yyss1, yysize * sizeof (*yyssp),
		    &yyvs1, yysize * sizeof (*yyvsp),

		    &yystacksize);

	yyss = yyss1;
	yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
	goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
	yystacksize = YYMAXDEPTH;

      {
	yytype_int16 *yyss1 = yyss;
	union yyalloc *yyptr =
	  (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
	if (! yyptr)
	  goto yyexhaustedlab;
	YYSTACK_RELOCATE (yyss);
	YYSTACK_RELOCATE (yyvs);

#  undef YYSTACK_RELOCATE
	if (yyss1 != yyssa)
	  YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;


      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
		  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
	YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     look-ahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to look-ahead token.  */
  yyn = yypact[yystate];
  if (yyn == YYPACT_NINF)
    goto yydefault;

  /* Not known => get a look-ahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid look-ahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = YYLEX;
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yyn == 0 || yyn == YYTABLE_NINF)
	goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  if (yyn == YYFINAL)
    YYACCEPT;

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the look-ahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token unless it is eof.  */
  if (yychar != YYEOF)
    yychar = YYEMPTY;

  yystate = yyn;
  *++yyvsp = yylval;

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     `$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 29:
#line 122 "smtparser.yy"
    { free( (yyvsp[(2) - (2)].str) ); }
    break;

  case 30:
#line 126 "smtparser.yy"
    {  }
    break;

  case 31:
#line 130 "smtparser.yy"
    { free( (yyvsp[(2) - (2)].str) ); }
    break;

  case 32:
#line 134 "smtparser.yy"
    { free( (yyvsp[(2) - (2)].str) ); }
    break;

  case 33:
#line 138 "smtparser.yy"
    { 
		      assert( false );
                      parser_ctx->SetInfo( NULL );
		      free( (yyvsp[(2) - (2)].str) ); 
		    }
    break;

  case 34:
#line 146 "smtparser.yy"
    { free( (yyvsp[(2) - (2)].str) ); }
    break;

  case 35:
#line 150 "smtparser.yy"
    { free( (yyvsp[(2) - (2)].str) ); }
    break;

  case 36:
#line 154 "smtparser.yy"
    { 
		    /*
                          if ( strcmp( $2, "EMPTY" ) == 0 ) parser_config->logic = EMPTY;
                     else if ( strcmp( $2, "QF_UF" ) == 0 ) parser_config->logic = QF_UF;
                     else if ( strcmp( $2, "QF_BV" ) == 0 ) parser_config->logic = QF_BV;
                     else if ( strcmp( $2, "QF_RDL" ) == 0 ) parser_config->logic = QF_RDL;
                     else if ( strcmp( $2, "QF_IDL" ) == 0 ) parser_config->logic = QF_IDL;
                     else if ( strcmp( $2, "QF_LRA" ) == 0 ) parser_config->logic = QF_LRA;
                     else if ( strcmp( $2, "QF_LIA" ) == 0 ) parser_config->logic = QF_LIA;
                     else if ( strcmp( $2, "QF_UFRDL" ) == 0 ) 
                     {
                       parser_config->logic = QF_UFRDL;
                       parser_config->incremental |= parser_config->satconfig.lazy_dtc != 0;
                     }
                     else if ( strcmp( $2, "QF_UFIDL" ) == 0 ) 
		     {
                       parser_config->logic = QF_UFIDL;
                       parser_config->incremental |= parser_config->satconfig.lazy_dtc != 0;
                     }
                     else if ( strcmp( $2, "QF_UFLRA" ) == 0 ) 
		     { 
                       parser_config->logic = QF_UFLRA; 
                       parser_config->lraconfig.gaussian_elim = parser_config->satconfig.lazy_dtc == 0; 
                       parser_config->incremental |= parser_config->satconfig.lazy_dtc != 0;
		     }
                     else if ( strcmp( $2, "QF_UFLIA" ) == 0 ) 
		     {
		       parser_config->logic = QF_UFLIA;
                       parser_config->incremental |= parser_config->satconfig.lazy_dtc != 0;
		     }
                     else if ( strcmp( $2, "QF_UFBV" ) == 0 ) parser_config->logic = QF_UFBV;
		     else if ( strcmp( $2, "QF_AX" ) == 0 ) 
		     { 
		       parser_config->logic = QF_AX;	
		       parser_config->incremental = 1;
		     }
                     else if ( strcmp( $2, "QF_AUFBV" ) == 0 ) parser_config->logic = QF_AUFBV;
// DO NOT REMOVE THIS COMMENT !!
// IT IS USED BY CREATE_THEORY.SH SCRIPT !!
// NEW_THEORY_INIT
		     parser_egraph->initializeStore( );
                    */
                     parser_ctx->SetLogic( (yyvsp[(2) - (2)].str) );
		     free( (yyvsp[(2) - (2)].str) ); 
                   }
    break;

  case 48:
#line 219 "smtparser.yy"
    { 
/* 
                    parser_egraph->newSort( $3 ); 
		    free( $3 ); 
*/
                  }
    break;

  case 50:
#line 230 "smtparser.yy"
    { 
                      /*
		      vector< unsigned > tmp;
		      tmp.push_back( DTYPE_BOOL );
		      parser_egraph->newSymbol( $3, tmp ); free( $3 ); 
		      Snode * s = parser_ctx->mkSortBool( );
		      parser_ctx->DeclareFun( $3, s ); free( $3 ); 
                      */
		    }
    break;

  case 51:
#line 240 "smtparser.yy"
    { 
                      /*
		      vector< unsigned > tmp;
		      tmp.push_back( DTYPE_BOOL );
		      parser_egraph->newSymbol( $2, tmp ); free( $2 ); 
		      Snode * s = parser_ctx->mkSortBool( );
		      parser_ctx->DeclareFun( $2, s ); free( $2 ); 
                      */
		    }
    break;

  case 53:
#line 255 "smtparser.yy"
    { 
                      /*
		      vector< unsigned > tmp;
		      tmp.push_back( DTYPE_REAL );
		      parser_egraph->newSymbol( $3, tmp ); free( $3 ); 
		      Snode * s = parser_ctx->mkSortReal( );
		      parser_ctx->DeclareFun( $3, s ); free( $3 ); 
                      */
		    }
    break;

  case 54:
#line 265 "smtparser.yy"
    { 
                      /*
		      vector< unsigned > tmp;
		      tmp.push_back( DTYPE_REAL );
		      parser_egraph->newSymbol( $2, tmp ); free( $2 ); 
		      Snode * s = parser_ctx->mkSortReal( );
		      parser_ctx->DeclareFun( $2, s ); free( $2 ); 
                      */
		    }
    break;

  case 56:
#line 280 "smtparser.yy"
    { 
                     /*
		     vector< unsigned > tmp;
		     tmp.push_back( DTYPE_INT );
		     parser_egraph->newSymbol( $3, tmp ); free( $3 ); 
		     Snode * s = parser_ctx->mkSortInt( );
		     parser_ctx->DeclareFun( $3, s ); free( $3 ); 
                     */
                   }
    break;

  case 57:
#line 290 "smtparser.yy"
    { 
                     /*
		     vector< unsigned > tmp;
		     tmp.push_back( DTYPE_INT );
		     parser_egraph->newSymbol( $2, tmp ); free( $2 ); 
		     Snode * s = parser_ctx->mkSortInt( );
		     parser_ctx->DeclareFun( $2, s ); free( $2 ); 
                     */
		   }
    break;

  case 59:
#line 305 "smtparser.yy"
    { 
/*
			if ( atoi( $6 ) > MAX_WIDTH ) error( "bitvector width too large, max is ", MAX_WIDTH );
			vector< unsigned > tmp;
			tmp.push_back( DTYPE_BITVEC | atoi( $6 ) );
			parser_egraph->newSymbol( $3, tmp ); free( $3 ); free( $6 ); 
*/
		      }
    break;

  case 60:
#line 314 "smtparser.yy"
    { 
/*
			if ( atoi( $5 ) > MAX_WIDTH ) error( "bitvector width too large, max is ", MAX_WIDTH );
			vector< unsigned > tmp;
			tmp.push_back( DTYPE_BITVEC | atoi( $5 ) );
			parser_egraph->newSymbol( $2, tmp ); free( $2 ); free( $5 ); 
*/
		      }
    break;

  case 67:
#line 339 "smtparser.yy"
    {
                      /*
		      vector< unsigned > tmp;
		      tmp.push_back( DTYPE_ARRAY );
		      parser_egraph->newSymbol( $3, tmp ); free( $3 );
		      Snode * s = parser_ctx->mkSortArray( );
		      parser_ctx->DeclareFun( $3, s ); free( $3 ); 
                      */
		     }
    break;

  case 68:
#line 349 "smtparser.yy"
    {
                      /*
		      vector< unsigned > tmp;
		      tmp.push_back( DTYPE_ARRAY );
		      parser_egraph->newSymbol( $2, tmp ); free( $2 ); 
		      Snode * s = parser_ctx->mkSortArray( );
		      parser_ctx->DeclareFun( $2, s ); free( $2 ); 
                      */
		     }
    break;

  case 69:
#line 359 "smtparser.yy"
    {
                      /*
		      vector< unsigned > tmp;
		      tmp.push_back( DTYPE_ARRAY | atoi( $7 ) );
		      parser_egraph->newSymbol( $2, tmp ); free( $2 ); 
		      Snode * s = parser_ctx->mkSortArray( );
		      parser_ctx->DeclareFun( $2, s ); free( $2 ); 
                      */
		     }
    break;

  case 70:
#line 371 "smtparser.yy"
    {
/*
		            vector< unsigned > tmp;
		            tmp.push_back( DTYPE_ARRAY_INDEX );
		            parser_egraph->newSymbol( $3, tmp ); free( $3 );
*/
			   }
    break;

  case 71:
#line 379 "smtparser.yy"
    {
/*
		            vector< unsigned > tmp;
		            tmp.push_back( DTYPE_ARRAY_INDEX );
		            parser_egraph->newSymbol( $2, tmp ); free( $2 );
*/
			   }
    break;

  case 72:
#line 388 "smtparser.yy"
    {
/*
			      vector< unsigned > tmp;
		              tmp.push_back( DTYPE_ARRAY_ELEMENT );
		              parser_egraph->newSymbol( $3, tmp ); free( $3 );
*/
			     }
    break;

  case 73:
#line 396 "smtparser.yy"
    {
/*
			      vector< unsigned > tmp;
		              tmp.push_back( DTYPE_ARRAY_ELEMENT );
		              parser_egraph->newSymbol( $2, tmp ); free( $2 );
*/
		 	     }
    break;

  case 74:
#line 485 "smtparser.yy"
    { parser_ctx->addAssert( (yyvsp[(3) - (3)].enode) ); }
    break;

  case 75:
#line 487 "smtparser.yy"
    { parser_ctx->addAssert( (yyvsp[(2) - (2)].enode) ); }
    break;

  case 76:
#line 491 "smtparser.yy"
    { /*parser_egraph->setTopEnode( $2 );*/ }
    break;

  case 77:
#line 495 "smtparser.yy"
    { 
#ifdef PRODUCE_PROOF
			 /*parser_egraph->addIFormula( ); */
#endif
                       }
    break;

  case 78:
#line 503 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkAnd( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 79:
#line 505 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkOr( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 80:
#line 507 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkImplies( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 81:
#line 509 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkNot( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 82:
#line 511 "smtparser.yy"
    { /*$$ = parser_ctx->mkIff( $3 );*/ }
    break;

  case 83:
#line 513 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkXor( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 84:
#line 515 "smtparser.yy"
    { /*$$ = parser_egraph->mkIfthenelse( $3, $4, $5 );*/ }
    break;

  case 85:
#line 517 "smtparser.yy"
    { (yyval.enode) = (yyvsp[(4) - (5)].enode); }
    break;

  case 86:
#line 519 "smtparser.yy"
    { (yyval.enode) = (yyvsp[(4) - (5)].enode); }
    break;

  case 87:
#line 521 "smtparser.yy"
    { /*$$ = parser_egraph->getDefine( $1 ); free( $1 );*/ }
    break;

  case 88:
#line 523 "smtparser.yy"
    { (yyval.enode) = (yyvsp[(1) - (1)].enode); }
    break;

  case 89:
#line 527 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkCons( (yyvsp[(1) - (2)].enode), (yyvsp[(2) - (2)].enode) ); }
    break;

  case 90:
#line 529 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkCons( (yyvsp[(1) - (1)].enode) ); }
    break;

  case 91:
#line 533 "smtparser.yy"
    { /*parser_ctx->mkDefine( $2, $3 ); free( $2 );*/ }
    break;

  case 92:
#line 536 "smtparser.yy"
    { /*parser_ctx->mkDefine( $2, $3 ); free( $2 );*/ }
    break;

  case 93:
#line 565 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkEq( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 94:
#line 567 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkDistinct( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 95:
#line 569 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkVar( (yyvsp[(1) - (1)].str), true ); free( (yyvsp[(1) - (1)].str) ); }
    break;

  case 96:
#line 571 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkTrue( ); }
    break;

  case 97:
#line 573 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkFalse( ); }
    break;

  case 98:
#line 575 "smtparser.yy"
    { /*$$ = parser_ctx->mkUp( $2, $3 ); free( $2 );*/ }
    break;

  case 99:
#line 579 "smtparser.yy"
    { (yyval.enode) = (yyvsp[(1) - (1)].enode); }
    break;

  case 100:
#line 589 "smtparser.yy"
    { /*$$ = parser_egraph->mkUf( $2, $3 ); free( $2 );*/ }
    break;

  case 101:
#line 593 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkCons( (yyvsp[(1) - (2)].enode), (yyvsp[(2) - (2)].enode) ); }
    break;

  case 102:
#line 595 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkCons( (yyvsp[(1) - (1)].enode) ); }
    break;

  case 103:
#line 607 "smtparser.yy"
    { /*$$ = parser_ctx->mkNum( $3, $4 ); free( $3 ); free( $4 );*/ }
    break;

  case 104:
#line 611 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkNum( (yyvsp[(1) - (1)].str) ); free( (yyvsp[(1) - (1)].str) ); }
    break;

  case 105:
#line 613 "smtparser.yy"
    { (yyval.enode) = parser_ctx->mkVar( (yyvsp[(1) - (1)].str), true ); free( (yyvsp[(1) - (1)].str) ); }
    break;

  case 106:
#line 615 "smtparser.yy"
    { /*$$ = parser_ctx->getDefine( $1 ); free( $1 );*/ }
    break;

  case 107:
#line 617 "smtparser.yy"
    { /*$$ = parser_ctx->mkIte( $3, $4, $5 );*/ }
    break;

  case 108:
#line 619 "smtparser.yy"
    { /*$$ = parser_ctx->mkUf( $2, $3 ); free( $2 );*/ }
    break;


/* Line 1267 of yacc.c.  */
#line 2215 "smtparser.cc"
      default: break;
    }
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;


  /* Now `shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*------------------------------------.
| yyerrlab -- here on detecting error |
`------------------------------------*/
yyerrlab:
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
      {
	YYSIZE_T yysize = yysyntax_error (0, yystate, yychar);
	if (yymsg_alloc < yysize && yymsg_alloc < YYSTACK_ALLOC_MAXIMUM)
	  {
	    YYSIZE_T yyalloc = 2 * yysize;
	    if (! (yysize <= yyalloc && yyalloc <= YYSTACK_ALLOC_MAXIMUM))
	      yyalloc = YYSTACK_ALLOC_MAXIMUM;
	    if (yymsg != yymsgbuf)
	      YYSTACK_FREE (yymsg);
	    yymsg = (char *) YYSTACK_ALLOC (yyalloc);
	    if (yymsg)
	      yymsg_alloc = yyalloc;
	    else
	      {
		yymsg = yymsgbuf;
		yymsg_alloc = sizeof yymsgbuf;
	      }
	  }

	if (0 < yysize && yysize <= yymsg_alloc)
	  {
	    (void) yysyntax_error (yymsg, yystate, yychar);
	    yyerror (yymsg);
	  }
	else
	  {
	    yyerror (YY_("syntax error"));
	    if (yysize != 0)
	      goto yyexhaustedlab;
	  }
      }
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse look-ahead token after an
	 error, discard it.  */

      if (yychar <= YYEOF)
	{
	  /* Return failure if at end of input.  */
	  if (yychar == YYEOF)
	    YYABORT;
	}
      else
	{
	  yydestruct ("Error: discarding",
		      yytoken, &yylval);
	  yychar = YYEMPTY;
	}
    }

  /* Else will try to reuse look-ahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule which action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;	/* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (yyn != YYPACT_NINF)
	{
	  yyn += YYTERROR;
	  if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
	    {
	      yyn = yytable[yyn];
	      if (0 < yyn)
		break;
	    }
	}

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
	YYABORT;


      yydestruct ("Error: popping",
		  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  if (yyn == YYFINAL)
    YYACCEPT;

  *++yyvsp = yylval;


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#ifndef yyoverflow
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEOF && yychar != YYEMPTY)
     yydestruct ("Cleanup: discarding lookahead",
		 yytoken, &yylval);
  /* Do not reclaim the symbols of the rule which action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
		  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  /* Make sure YYID is used.  */
  return YYID (yyresult);
}


#line 774 "smtparser.yy"


//=======================================================================================
// Auxiliary Routines

vector< unsigned > * createTypeList( unsigned t )
{
  vector< unsigned > * l = new vector< unsigned >;
  l->push_back( t );
  return l;
} 

vector< unsigned > * createTypeList( unsigned t, const char * size )
{
/*
  assert( t == DTYPE_BITVEC );
*/
  vector< unsigned > * l = new vector< unsigned >;
  const unsigned int_size = atoi( size ); 
  assert( int_size <= MAX_WIDTH );
  l->push_back( t | int_size );
  return l;
} 

vector< unsigned > * pushTypeList( vector< unsigned > * l, unsigned t )
{
  l->push_back( t );
  return l;
}

vector< unsigned > * pushTypeList( vector< unsigned > * l, unsigned t, const char * size )
{
  const unsigned int_size = atoi( size );
  assert( int_size <= MAX_WIDTH );
  l->push_back( t | int_size );
  return l;
}

void destroyTypeList( vector< unsigned > * l )
{
  delete l;
}

