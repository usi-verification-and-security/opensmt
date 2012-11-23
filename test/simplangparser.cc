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
#define YYPURE 1

/* Using locations.  */
#define YYLSP_NEEDED 1

/* Substitute the variable and function names.  */
#define yyparse simplangparse
#define yylex   simplanglex
#define yyerror simplangerror
#define yylval  simplanglval
#define yychar  simplangchar
#define yydebug simplangdebug
#define yynerrs simplangnerrs
#define yylloc simplanglloc

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
     TK_NUM = 286,
     TK_SYM = 287,
     TK_KEY = 288,
     TK_STR = 289,
     TK_DEC = 290,
     TK_HEX = 291,
     TK_BIN = 292,
     KW_SORTS = 293,
     KW_FUNS = 294,
     KW_SORTSDESCRIPTION = 295,
     KW_FUNSDESCRIPTION = 296,
     KW_DEFINITION = 297,
     KW_NOTES = 298,
     KW_THEORIES = 299,
     KW_LANGUAGE = 300,
     KW_EXTENSIONS = 301,
     KW_VALUES = 302,
     KW_PRINTSUCCESS = 303,
     KW_EXPANDDEFINITIONS = 304,
     KW_INTERACTIVEMODE = 305,
     KW_PRODUCEPROOFS = 306,
     KW_PRODUCEUNSATCORES = 307,
     KW_PRODUCEMODELS = 308,
     KW_PRODUCEASSIGNMENTS = 309,
     KW_REGULAROUTPUTCHANNEL = 310,
     KW_DIAGNOSTICOUTPUTCHANNEL = 311,
     KW_RANDOMSEED = 312,
     KW_VERBOSITY = 313,
     KW_ERRORBEHAVIOR = 314,
     KW_NAME = 315,
     KW_AUTHORS = 316,
     KW_VERSION = 317,
     KW_STATUS = 318,
     KW_REASONUNKNOWN = 319,
     KW_ALLSTATISTICS = 320
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
#define TK_NUM 286
#define TK_SYM 287
#define TK_KEY 288
#define TK_STR 289
#define TK_DEC 290
#define TK_HEX 291
#define TK_BIN 292
#define KW_SORTS 293
#define KW_FUNS 294
#define KW_SORTSDESCRIPTION 295
#define KW_FUNSDESCRIPTION 296
#define KW_DEFINITION 297
#define KW_NOTES 298
#define KW_THEORIES 299
#define KW_LANGUAGE 300
#define KW_EXTENSIONS 301
#define KW_VALUES 302
#define KW_PRINTSUCCESS 303
#define KW_EXPANDDEFINITIONS 304
#define KW_INTERACTIVEMODE 305
#define KW_PRODUCEPROOFS 306
#define KW_PRODUCEUNSATCORES 307
#define KW_PRODUCEMODELS 308
#define KW_PRODUCEASSIGNMENTS 309
#define KW_REGULAROUTPUTCHANNEL 310
#define KW_DIAGNOSTICOUTPUTCHANNEL 311
#define KW_RANDOMSEED 312
#define KW_VERBOSITY 313
#define KW_ERRORBEHAVIOR 314
#define KW_NAME 315
#define KW_AUTHORS 316
#define KW_VERSION 317
#define KW_STATUS 318
#define KW_REASONUNKNOWN 319
#define KW_ALLSTATISTICS 320




/* Copy the first part of user declarations.  */
#line 9 "simplangparser.yy"

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <vector>
#include <list>
#include <string>
#include <string.h>

#include "simplangcontext.h"
#include "simplangparser.h"


int simplanglex(YYSTYPE* lvalp, YYLTYPE* llocp, void* scanner);

void simplangerror( YYLTYPE* locp, SimplangContext* context, const char * s )
{
  printf( "At line %d: %s\n", locp->first_line, s );
  exit( 1 );
}

#define scanner context->scanner

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
#line 37 "simplangparser.yy"
{
  char  *                   str;
  vector< string > *        str_list;
  ASTNode *                 snode;
  list< ASTNode * > *       snode_list;
}
/* Line 193 of yacc.c.  */
#line 268 "simplangparser.cc"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
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


/* Copy the second part of user declarations.  */


/* Line 216 of yacc.c.  */
#line 293 "simplangparser.cc"

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
	 || (defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL \
	     && defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss;
  YYSTYPE yyvs;
    YYLTYPE yyls;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE) + sizeof (YYLTYPE)) \
      + 2 * YYSTACK_GAP_MAXIMUM)

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
#define YYFINAL  3
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   313

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  70
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  26
/* YYNRULES -- Number of rules.  */
#define YYNRULES  120
/* YYNRULES -- Number of states.  */
#define YYNSTATES  223

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   320

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    69,     2,     2,     2,     2,     2,     2,
      66,    67,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,    68,     2,     2,     2,     2,
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
      65
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     5,     6,     9,    14,    19,    24,    30,
      39,    48,    58,    63,    68,    73,    77,    81,    85,    89,
      97,   101,   106,   111,   116,   120,   121,   124,   126,   129,
     131,   134,   136,   138,   142,   144,   150,   152,   158,   161,
     162,   164,   166,   168,   172,   173,   176,   178,   180,   182,
     184,   186,   189,   191,   193,   199,   200,   203,   208,   209,
     212,   217,   218,   221,   223,   225,   231,   240,   249,   258,
     263,   264,   267,   269,   272,   275,   278,   281,   284,   287,
     290,   293,   296,   299,   302,   304,   306,   308,   310,   312,
     314,   316,   318,   320,   322,   324,   326,   328,   330,   332,
     334,   336,   338,   340,   342,   344,   346,   348,   350,   352,
     354,   356,   358,   360,   362,   364,   366,   368,   370,   372,
     374
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int8 yyrhs[] =
{
      71,     0,    -1,    72,    -1,    -1,    72,    73,    -1,    66,
      27,    32,    67,    -1,    66,    29,    93,    67,    -1,    66,
      28,    75,    67,    -1,    66,    13,    32,    31,    67,    -1,
      66,    15,    32,    66,    91,    67,    78,    67,    -1,    66,
      14,    32,    66,    79,    67,    78,    67,    -1,    66,    16,
      32,    66,    87,    67,    78,    90,    67,    -1,    66,    26,
      31,    67,    -1,    66,    25,    31,    67,    -1,    66,    11,
      90,    67,    -1,    66,    12,    67,    -1,    66,    18,    67,
      -1,    66,    22,    67,    -1,    66,    23,    67,    -1,    66,
      24,    66,    90,    89,    67,    67,    -1,    66,    19,    67,
      -1,    66,    21,    33,    67,    -1,    66,    21,    94,    67,
      -1,    66,    20,    95,    67,    -1,    66,    17,    67,    -1,
      -1,    74,    75,    -1,    33,    -1,    33,    76,    -1,    94,
      -1,    94,    76,    -1,    82,    -1,    32,    -1,    66,    81,
      67,    -1,    32,    -1,    66,    68,    32,    83,    67,    -1,
      77,    -1,    66,    77,    78,    79,    67,    -1,    79,    78,
      -1,    -1,    82,    -1,    32,    -1,    33,    -1,    66,    81,
      67,    -1,    -1,    81,    80,    -1,    31,    -1,    35,    -1,
      36,    -1,    37,    -1,    34,    -1,    83,    31,    -1,    31,
      -1,    77,    -1,    66,     3,    77,    78,    67,    -1,    -1,
      85,    86,    -1,    66,    32,    90,    67,    -1,    -1,    87,
      88,    -1,    66,    32,    78,    67,    -1,    -1,    89,    90,
      -1,    82,    -1,    84,    -1,    66,    84,    90,    89,    67,
      -1,    66,     7,    66,    86,    85,    67,    90,    67,    -1,
      66,     6,    66,    88,    87,    67,    90,    67,    -1,    66,
       5,    66,    88,    87,    67,    90,    67,    -1,    69,    90,
      75,    74,    -1,    -1,    91,    32,    -1,    32,    -1,    48,
      92,    -1,    49,    92,    -1,    50,    92,    -1,    51,    92,
      -1,    52,    92,    -1,    53,    92,    -1,    54,    92,    -1,
      55,    34,    -1,    56,    34,    -1,    57,    31,    -1,    58,
      31,    -1,    75,    -1,    38,    -1,    39,    -1,    40,    -1,
      41,    -1,    42,    -1,    47,    -1,    43,    -1,    44,    -1,
      45,    -1,    46,    -1,    48,    -1,    49,    -1,    50,    -1,
      51,    -1,    52,    -1,    53,    -1,    54,    -1,    55,    -1,
      56,    -1,    57,    -1,    58,    -1,    59,    -1,    60,    -1,
      61,    -1,    62,    -1,    63,    -1,    64,    -1,    65,    -1,
      59,    -1,    60,    -1,    61,    -1,    62,    -1,    63,    -1,
      64,    -1,    65,    -1,    33,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,    66,    66,    70,    71,    75,    81,    87,    93,   100,
     113,   125,   138,   144,   150,   156,   160,   164,   168,   172,
     178,   182,   188,   194,   200,   205,   206,   210,   212,   214,
     216,   220,   222,   226,   233,   235,   239,   241,   249,   252,
     255,   261,   265,   269,   277,   280,   287,   289,   291,   293,
     295,   299,   301,   305,   307,   317,   318,   322,   327,   328,
     332,   336,   337,   341,   343,   345,   351,   361,   371,   381,
     456,   457,   614,   627,   633,   639,   645,   651,   657,   663,
     669,   675,   681,   687,   693,   701,   703,   705,   707,   709,
     711,   713,   715,   717,   719,   721,   723,   725,   727,   729,
     731,   733,   735,   737,   739,   741,   743,   745,   747,   749,
     751,   753,   755,   759,   761,   763,   765,   767,   769,   771,
     773
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "TK_AS", "TK_DECIMAL", "TK_EXISTS",
  "TK_FORALL", "TK_LET", "TK_NUMERAL", "TK_PAR", "TK_STRING", "TK_ASSERT",
  "TK_CHECKSAT", "TK_DECLARESORT", "TK_DECLAREFUN", "TK_DEFINESORT",
  "TK_DEFINEFUN", "TK_EXIT", "TK_GETASSERTIONS", "TK_GETASSIGNMENT",
  "TK_GETINFO", "TK_GETOPTION", "TK_GETPROOF", "TK_GETUNSATCORE",
  "TK_GETVALUE", "TK_POP", "TK_PUSH", "TK_SETLOGIC", "TK_SETINFO",
  "TK_SETOPTION", "TK_THEORY", "TK_NUM", "TK_SYM", "TK_KEY", "TK_STR",
  "TK_DEC", "TK_HEX", "TK_BIN", "KW_SORTS", "KW_FUNS",
  "KW_SORTSDESCRIPTION", "KW_FUNSDESCRIPTION", "KW_DEFINITION", "KW_NOTES",
  "KW_THEORIES", "KW_LANGUAGE", "KW_EXTENSIONS", "KW_VALUES",
  "KW_PRINTSUCCESS", "KW_EXPANDDEFINITIONS", "KW_INTERACTIVEMODE",
  "KW_PRODUCEPROOFS", "KW_PRODUCEUNSATCORES", "KW_PRODUCEMODELS",
  "KW_PRODUCEASSIGNMENTS", "KW_REGULAROUTPUTCHANNEL",
  "KW_DIAGNOSTICOUTPUTCHANNEL", "KW_RANDOMSEED", "KW_VERBOSITY",
  "KW_ERRORBEHAVIOR", "KW_NAME", "KW_AUTHORS", "KW_VERSION", "KW_STATUS",
  "KW_REASONUNKNOWN", "KW_ALLSTATISTICS", "'('", "')'", "'_'", "'!'",
  "$accept", "script", "command_list", "command", "attribute_list",
  "attribute", "attribute_value", "identifier", "sort", "sort_list",
  "s_expr", "s_expr_list", "spec_const", "numeral_list", "qual_identifier",
  "var_binding_list", "var_binding", "sorted_var_list", "sorted_var",
  "term_list", "term", "symbol_list", "b_value", "option", "predef_key",
  "info_flag", 0
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
     315,   316,   317,   318,   319,   320,    40,    41,    95,    33
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    70,    71,    72,    72,    73,    73,    73,    73,    73,
      73,    73,    73,    73,    73,    73,    73,    73,    73,    73,
      73,    73,    73,    73,    73,    74,    74,    75,    75,    75,
      75,    76,    76,    76,    77,    77,    78,    78,    79,    79,
      80,    80,    80,    80,    81,    81,    82,    82,    82,    82,
      82,    83,    83,    84,    84,    85,    85,    86,    87,    87,
      88,    89,    89,    90,    90,    90,    90,    90,    90,    90,
      91,    91,    92,    93,    93,    93,    93,    93,    93,    93,
      93,    93,    93,    93,    93,    94,    94,    94,    94,    94,
      94,    94,    94,    94,    94,    94,    94,    94,    94,    94,
      94,    94,    94,    94,    94,    94,    94,    94,    94,    94,
      94,    94,    94,    95,    95,    95,    95,    95,    95,    95,
      95
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     0,     2,     4,     4,     4,     5,     8,
       8,     9,     4,     4,     4,     3,     3,     3,     3,     7,
       3,     4,     4,     4,     3,     0,     2,     1,     2,     1,
       2,     1,     1,     3,     1,     5,     1,     5,     2,     0,
       1,     1,     1,     3,     0,     2,     1,     1,     1,     1,
       1,     2,     1,     1,     5,     0,     2,     4,     0,     2,
       4,     0,     2,     1,     1,     5,     8,     8,     8,     4,
       0,     2,     1,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       3,     0,     2,     1,     0,     4,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    46,    34,    50,    47,    48,
      49,     0,     0,    53,    63,    64,     0,    15,     0,     0,
       0,     0,    24,    16,    20,   120,   113,   114,   115,   116,
     117,   118,   119,     0,     0,    85,    86,    87,    88,    89,
      91,    92,    93,    94,    90,    95,    96,    97,    98,    99,
     100,   101,   102,   103,   104,   105,   106,   107,   108,   109,
     110,   111,   112,     0,    17,    18,     0,     0,     0,     0,
      27,     0,    29,    95,    96,    97,    98,    99,   100,   101,
     102,   103,   104,   105,    84,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    14,     0,    39,    70,    58,    23,
      21,    22,    61,    13,    12,     5,    32,    44,    28,    31,
       7,    30,    72,    73,    74,    75,    76,    77,    78,    79,
      80,    81,    82,    83,     6,     0,     0,     0,     0,     0,
       0,    61,    25,     8,     0,     0,     0,     0,     0,     0,
      36,     0,     0,    58,    58,     0,    55,    52,     0,     0,
      69,     0,    38,    71,     0,     0,    59,     0,    62,    41,
      42,    44,    33,    45,    40,     0,    54,     0,     0,     0,
       0,     0,    51,    35,    65,    26,     0,     0,     0,    19,
       0,    39,     0,     0,     0,     0,     0,    56,    10,     9,
       0,    43,     0,    60,     0,     0,    57,     0,    11,    37,
      68,    67,    66
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     1,     2,     5,   170,    91,   128,    33,   172,   154,
     183,   158,    34,   168,    35,   191,   166,   156,   176,   157,
     178,   155,   133,   105,    92,    53
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -142
static const yytype_int16 yypact[] =
{
    -142,     8,   -50,  -142,   284,  -142,    65,   -43,    -3,     0,
      13,    16,     2,    14,    20,   109,   163,    21,    22,    -2,
      36,    52,    59,   196,   229,  -142,  -142,  -142,  -142,  -142,
    -142,     7,    65,  -142,  -142,  -142,    27,  -142,    67,    37,
      38,    39,  -142,  -142,  -142,  -142,  -142,  -142,  -142,  -142,
    -142,  -142,  -142,    40,    41,  -142,  -142,  -142,  -142,  -142,
    -142,  -142,  -142,  -142,  -142,  -142,  -142,  -142,  -142,  -142,
    -142,  -142,  -142,  -142,  -142,  -142,  -142,  -142,  -142,  -142,
    -142,  -142,  -142,    43,  -142,  -142,    65,    44,    60,    61,
     101,    62,   101,    98,    98,    98,    98,    98,    98,    98,
     105,   106,   110,   112,  -142,    77,   -25,    79,    80,    84,
       6,   119,    65,   196,  -142,    85,  -142,  -142,  -142,  -142,
    -142,  -142,  -142,  -142,  -142,  -142,  -142,  -142,  -142,  -142,
    -142,  -142,  -142,  -142,  -142,  -142,  -142,  -142,  -142,  -142,
    -142,  -142,  -142,  -142,  -142,    86,    -7,    87,    87,    97,
     133,  -142,  -142,  -142,   -17,   -13,   -39,   -14,    82,   -26,
    -142,    99,   143,  -142,  -142,   144,  -142,  -142,   -20,    26,
     196,    -7,  -142,  -142,    -7,    -7,  -142,   111,  -142,  -142,
    -142,  -142,  -142,  -142,  -142,    -7,  -142,    -7,   -31,   -29,
      65,    10,  -142,  -142,  -142,  -142,   113,   114,    65,  -142,
      89,  -142,   115,    65,    65,   116,    65,  -142,  -142,  -142,
     118,  -142,    -1,  -142,   120,   121,  -142,   122,  -142,  -142,
    -142,  -142,  -142
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -142,  -142,  -142,  -142,  -142,   -23,    73,  -103,  -141,   -24,
    -142,     5,   -88,  -142,   148,  -142,     3,   -85,   -62,    42,
      -6,  -142,    63,  -142,   174,  -142
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -1
static const yytype_uint8 yytable[] =
{
      36,   104,   129,   146,   129,   161,    26,    26,     3,   106,
     106,   192,   107,   108,   109,    26,     4,    25,    26,   173,
      27,    28,    29,    30,    37,    26,   113,   162,   175,    38,
     196,    26,    39,   197,   198,   162,   203,   162,   204,    26,
     145,   145,   111,   160,   201,    40,   202,   193,    41,   159,
     171,   160,    31,   177,   174,    32,   185,    25,    26,   159,
      27,    28,    29,    30,    86,   159,   219,    87,   160,    42,
     184,   160,   160,   110,   111,   111,   165,   206,   188,   189,
     122,    43,   160,    88,   160,   163,   164,    44,    84,    85,
     152,    89,    31,   194,   114,    32,    25,    26,   115,    27,
      28,    29,    30,   116,   117,   118,   151,   119,   120,   160,
     121,   123,   184,    25,   179,   180,    27,    28,    29,    30,
      25,   179,   180,    27,    28,    29,    30,   124,   125,   130,
     132,    31,    25,   126,    32,    27,    28,    29,    30,   140,
     141,   142,    45,   143,   144,   147,   148,   195,   181,   182,
     149,   150,   153,   162,   111,   181,   211,   134,   135,   136,
     137,   138,   139,   165,   167,   131,   186,   127,    46,    47,
      48,    49,    50,    51,    52,   187,   190,   212,   199,   112,
     208,   209,   213,   216,   205,   218,   200,   220,   221,   222,
      83,     0,   210,   169,   207,     0,    54,   214,   215,     0,
     217,    55,    56,    57,    58,    59,    60,    61,    62,    63,
      64,    65,    66,    67,    68,    69,    70,    71,    72,    73,
      74,    75,    76,    77,    78,    79,    80,    81,    82,    90,
       0,     0,     0,     0,    55,    56,    57,    58,    59,    60,
      61,    62,    63,    64,    65,    66,    67,    68,    69,    70,
      71,    72,    73,    74,    75,    76,    77,    78,    79,    80,
      81,    82,    90,     0,     0,     0,     0,    55,    56,    57,
      58,    59,    60,    61,    62,    63,    64,    93,    94,    95,
      96,    97,    98,    99,   100,   101,   102,   103,    76,    77,
      78,    79,    80,    81,    82,     6,     7,     8,     9,    10,
      11,    12,    13,    14,    15,    16,    17,    18,    19,    20,
      21,    22,    23,    24
};

static const yytype_int16 yycheck[] =
{
       6,    24,    90,   106,    92,   146,    32,    32,     0,     3,
       3,    31,     5,     6,     7,    32,    66,    31,    32,    32,
      34,    35,    36,    37,    67,    32,    32,    66,    67,    32,
     171,    32,    32,   174,   175,    66,    67,    66,    67,    32,
      66,    66,    68,   146,   185,    32,   187,    67,    32,    66,
      67,   154,    66,    67,    67,    69,   159,    31,    32,    66,
      34,    35,    36,    37,    66,    66,    67,    31,   171,    67,
     158,   174,   175,    66,    68,    68,    66,    67,   163,   164,
      86,    67,   185,    31,   187,   147,   148,    67,    67,    67,
     113,    32,    66,    67,    67,    69,    31,    32,    31,    34,
      35,    36,    37,    66,    66,    66,   112,    67,    67,   212,
      67,    67,   200,    31,    32,    33,    34,    35,    36,    37,
      31,    32,    33,    34,    35,    36,    37,    67,    67,    67,
      32,    66,    31,    32,    69,    34,    35,    36,    37,    34,
      34,    31,    33,    31,    67,    66,    66,   170,    66,    67,
      66,    32,    67,    66,    68,    66,    67,    94,    95,    96,
      97,    98,    99,    66,    31,    92,    67,    66,    59,    60,
      61,    62,    63,    64,    65,    32,    32,   201,    67,    31,
      67,    67,    67,    67,   190,    67,   181,    67,    67,    67,
      16,    -1,   198,   151,   191,    -1,    33,   203,   204,    -1,
     206,    38,    39,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,    51,    52,    53,    54,    55,    56,
      57,    58,    59,    60,    61,    62,    63,    64,    65,    33,
      -1,    -1,    -1,    -1,    38,    39,    40,    41,    42,    43,
      44,    45,    46,    47,    48,    49,    50,    51,    52,    53,
      54,    55,    56,    57,    58,    59,    60,    61,    62,    63,
      64,    65,    33,    -1,    -1,    -1,    -1,    38,    39,    40,
      41,    42,    43,    44,    45,    46,    47,    48,    49,    50,
      51,    52,    53,    54,    55,    56,    57,    58,    59,    60,
      61,    62,    63,    64,    65,    11,    12,    13,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    27,    28,    29
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    71,    72,     0,    66,    73,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    31,    32,    34,    35,    36,
      37,    66,    69,    77,    82,    84,    90,    67,    32,    32,
      32,    32,    67,    67,    67,    33,    59,    60,    61,    62,
      63,    64,    65,    95,    33,    38,    39,    40,    41,    42,
      43,    44,    45,    46,    47,    48,    49,    50,    51,    52,
      53,    54,    55,    56,    57,    58,    59,    60,    61,    62,
      63,    64,    65,    94,    67,    67,    66,    31,    31,    32,
      33,    75,    94,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    75,    93,     3,     5,     6,     7,
      66,    68,    84,    90,    67,    31,    66,    66,    66,    67,
      67,    67,    90,    67,    67,    67,    32,    66,    76,    82,
      67,    76,    32,    92,    92,    92,    92,    92,    92,    92,
      34,    34,    31,    31,    67,    66,    77,    66,    66,    66,
      32,    90,    75,    67,    79,    91,    87,    89,    81,    66,
      77,    78,    66,    88,    88,    66,    86,    31,    83,    89,
      74,    67,    78,    32,    67,    67,    88,    67,    90,    32,
      33,    66,    67,    80,    82,    77,    67,    32,    87,    87,
      32,    85,    31,    67,    67,    75,    78,    78,    78,    67,
      81,    78,    78,    67,    67,    90,    67,    86,    67,    67,
      90,    67,    79,    67,    90,    90,    67,    90,    67,    67,
      67,    67,    67
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
      yyerror (&yylloc, context, YY_("syntax error: cannot back up")); \
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
# define YYLEX yylex (&yylval, &yylloc, YYLEX_PARAM)
#else
# define YYLEX yylex (&yylval, &yylloc, scanner)
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
		  Type, Value, Location, context); \
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
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, SimplangContext* context)
#else
static void
yy_symbol_value_print (yyoutput, yytype, yyvaluep, yylocationp, context)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
    YYLTYPE const * const yylocationp;
    SimplangContext* context;
#endif
{
  if (!yyvaluep)
    return;
  YYUSE (yylocationp);
  YYUSE (context);
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
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, SimplangContext* context)
#else
static void
yy_symbol_print (yyoutput, yytype, yyvaluep, yylocationp, context)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
    YYLTYPE const * const yylocationp;
    SimplangContext* context;
#endif
{
  if (yytype < YYNTOKENS)
    YYFPRINTF (yyoutput, "token %s (", yytname[yytype]);
  else
    YYFPRINTF (yyoutput, "nterm %s (", yytname[yytype]);

  YY_LOCATION_PRINT (yyoutput, *yylocationp);
  YYFPRINTF (yyoutput, ": ");
  yy_symbol_value_print (yyoutput, yytype, yyvaluep, yylocationp, context);
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
yy_reduce_print (YYSTYPE *yyvsp, YYLTYPE *yylsp, int yyrule, SimplangContext* context)
#else
static void
yy_reduce_print (yyvsp, yylsp, yyrule, context)
    YYSTYPE *yyvsp;
    YYLTYPE *yylsp;
    int yyrule;
    SimplangContext* context;
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
		       , &(yylsp[(yyi + 1) - (yynrhs)])		       , context);
      fprintf (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (yydebug)				\
    yy_reduce_print (yyvsp, yylsp, Rule, context); \
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
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, YYLTYPE *yylocationp, SimplangContext* context)
#else
static void
yydestruct (yymsg, yytype, yyvaluep, yylocationp, context)
    const char *yymsg;
    int yytype;
    YYSTYPE *yyvaluep;
    YYLTYPE *yylocationp;
    SimplangContext* context;
#endif
{
  YYUSE (yyvaluep);
  YYUSE (yylocationp);
  YYUSE (context);

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
int yyparse (SimplangContext* context);
#else
int yyparse ();
#endif
#endif /* ! YYPARSE_PARAM */






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
yyparse (SimplangContext* context)
#else
int
yyparse (context)
    SimplangContext* context;
#endif
#endif
{
  /* The look-ahead symbol.  */
int yychar;

/* The semantic value of the look-ahead symbol.  */
YYSTYPE yylval;

/* Number of syntax errors so far.  */
int yynerrs;
/* Location data for the look-ahead symbol.  */
YYLTYPE yylloc;

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

  /* The location stack.  */
  YYLTYPE yylsa[YYINITDEPTH];
  YYLTYPE *yyls = yylsa;
  YYLTYPE *yylsp;
  /* The locations where the error started and ended.  */
  YYLTYPE yyerror_range[2];

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N), yylsp -= (N))

  YYSIZE_T yystacksize = YYINITDEPTH;

  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;
  YYLTYPE yyloc;

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
  yylsp = yyls;
#if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL
  /* Initialize the default location before parsing starts.  */
  yylloc.first_line   = yylloc.last_line   = 1;
  yylloc.first_column = yylloc.last_column = 0;
#endif

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
	YYLTYPE *yyls1 = yyls;

	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if yyoverflow is a macro.  */
	yyoverflow (YY_("memory exhausted"),
		    &yyss1, yysize * sizeof (*yyssp),
		    &yyvs1, yysize * sizeof (*yyvsp),
		    &yyls1, yysize * sizeof (*yylsp),
		    &yystacksize);
	yyls = yyls1;
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
	YYSTACK_RELOCATE (yyls);
#  undef YYSTACK_RELOCATE
	if (yyss1 != yyssa)
	  YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;
      yylsp = yyls + yysize - 1;

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
  *++yylsp = yylloc;
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

  /* Default location.  */
  YYLLOC_DEFAULT (yyloc, (yylsp - yylen), yylen);
  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 66 "simplangparser.yy"
    { ASTNode *n = new ASTNode(CMDL_T, "main-script"); n->children = (yyvsp[(1) - (1)].snode_list); context->insertRoot(n); }
    break;

  case 3:
#line 70 "simplangparser.yy"
    { (yyval.snode_list) = new list<ASTNode*>(); }
    break;

  case 4:
#line 72 "simplangparser.yy"
    { (*(yyvsp[(1) - (2)].snode_list)).push_back((yyvsp[(2) - (2)].snode)); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 5:
#line 76 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[(3) - (4)].str)));
        }
    break;

  case 6:
#line 82 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(3) - (4)].snode));
        }
    break;

  case 7:
#line 88 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(3) - (4)].snode));
        }
    break;

  case 8:
#line 94 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (5)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[(3) - (5)].str)));
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[(4) - (5)].str)));
        }
    break;

  case 9:
#line 101 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (8)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[(3) - (8)].str)));

            ASTNode* syml = new ASTNode(SYML_T, NULL);
            syml->children = (yyvsp[(5) - (8)].snode_list);
            (yyval.snode)->children->push_back(syml);

            (yyval.snode)->children->push_back((yyvsp[(7) - (8)].snode));
        }
    break;

  case 10:
#line 114 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (8)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[(3) - (8)].str)));

            ASTNode* sortl = new ASTNode(SORTL_T, NULL);
            sortl->children = (yyvsp[(5) - (8)].snode_list);
            (yyval.snode)->children->push_back(sortl);

            (yyval.snode)->children->push_back((yyvsp[(7) - (8)].snode));
        }
    break;

  case 11:
#line 126 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (9)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[(3) - (9)].str)));

            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = (yyvsp[(5) - (9)].snode_list);
            (yyval.snode)->children->push_back(svl);

            (yyval.snode)->children->push_back((yyvsp[(7) - (9)].snode));
            (yyval.snode)->children->push_back((yyvsp[(8) - (9)].snode));
        }
    break;

  case 12:
#line 139 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[(3) - (4)].str)));
        }
    break;

  case 13:
#line 145 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[(3) - (4)].str)));
        }
    break;

  case 14:
#line 151 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(3) - (4)].snode));
        }
    break;

  case 15:
#line 157 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (3)].str));
        }
    break;

  case 16:
#line 161 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (3)].str));
        }
    break;

  case 17:
#line 165 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (3)].str));
        }
    break;

  case 18:
#line 169 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (3)].str));
        }
    break;

  case 19:
#line 173 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (7)].str));
            (yyval.snode)->children = (yyvsp[(5) - (7)].snode_list);
            (yyval.snode)->children->push_front((yyvsp[(4) - (7)].snode));
        }
    break;

  case 20:
#line 179 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (3)].str));
        }
    break;

  case 21:
#line 183 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[(3) - (4)].str)));
        }
    break;

  case 22:
#line 189 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(PATTR_T, (yyvsp[(3) - (4)].str)));
        }
    break;

  case 23:
#line 195 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(3) - (4)].snode));
        }
    break;

  case 24:
#line 201 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (3)].str)); }
    break;

  case 25:
#line 205 "simplangparser.yy"
    { (yyval.snode_list) = new list<ASTNode*>(); }
    break;

  case 26:
#line 207 "simplangparser.yy"
    { (yyvsp[(1) - (2)].snode_list)->push_back((yyvsp[(2) - (2)].snode)); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 27:
#line 211 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(UATTR_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 28:
#line 213 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(UATTR_T, (yyvsp[(1) - (2)].str)); (yyval.snode)->children = new list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode)); }
    break;

  case 29:
#line 215 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(PATTR_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 30:
#line 217 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(PATTR_T, (yyvsp[(1) - (2)].str)); (yyval.snode)->children = new list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode)); }
    break;

  case 31:
#line 221 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(SPECC_T, NULL); (yyval.snode)->children = new list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(1) - (1)].snode)); }
    break;

  case 32:
#line 223 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(SYM_T, (yyvsp[(1) - (1)].str));
        }
    break;

  case 33:
#line 227 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(SEXPRL_T, NULL);
            (yyval.snode)->children = (yyvsp[(2) - (3)].snode_list);
        }
    break;

  case 34:
#line 234 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(SYM_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 35:
#line 236 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(SYM_T, (yyvsp[(3) - (5)].str)); (yyval.snode)->children = (yyvsp[(4) - (5)].snode_list); }
    break;

  case 36:
#line 240 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(ID_T, NULL); (yyval.snode)->children = new list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(1) - (1)].snode)); }
    break;

  case 37:
#line 242 "simplangparser.yy"
    {
        (yyval.snode) = new ASTNode(LID_T, NULL);
        (yyval.snode)->children = (yyvsp[(4) - (5)].snode_list);
        (yyval.snode)->children->push_front((yyvsp[(3) - (5)].snode));
      }
    break;

  case 38:
#line 250 "simplangparser.yy"
    { (yyvsp[(1) - (2)].snode_list)->push_back((yyvsp[(2) - (2)].snode)); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 39:
#line 252 "simplangparser.yy"
    { (yyval.snode_list) = new list<ASTNode*>(); }
    break;

  case 40:
#line 256 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(SPECC_T, NULL);
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(1) - (1)].snode));
        }
    break;

  case 41:
#line 262 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(SYM_T, (yyvsp[(1) - (1)].str));
        }
    break;

  case 42:
#line 266 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(UATTR_T, (yyvsp[(1) - (1)].str));
        }
    break;

  case 43:
#line 270 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(SEXPRL_T, NULL);
            (yyval.snode)->children = (yyvsp[(2) - (3)].snode_list);
        }
    break;

  case 44:
#line 277 "simplangparser.yy"
    {
            (yyval.snode_list) = new list<ASTNode*>();
        }
    break;

  case 45:
#line 281 "simplangparser.yy"
    {
            (yyvsp[(1) - (2)].snode_list)->push_back((yyvsp[(2) - (2)].snode));
            (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list);
        }
    break;

  case 46:
#line 288 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(NUM_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 47:
#line 290 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(DEC_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 48:
#line 292 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(HEX_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 49:
#line 294 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(BIN_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 50:
#line 296 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(STR_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 51:
#line 300 "simplangparser.yy"
    { (yyvsp[(1) - (2)].snode_list)->push_back(new ASTNode(NUM_T, (yyvsp[(2) - (2)].str))); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 52:
#line 302 "simplangparser.yy"
    { (yyval.snode_list) = new list<ASTNode*>(); (yyval.snode_list)->push_back(new ASTNode(NUM_T, (yyvsp[(1) - (1)].str))); }
    break;

  case 53:
#line 306 "simplangparser.yy"
    { (yyval.snode) = (yyvsp[(1) - (1)].snode); }
    break;

  case 54:
#line 308 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(AS_T, NULL);
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(3) - (5)].snode));
            (yyval.snode)->children->push_back((yyvsp[(4) - (5)].snode));
        }
    break;

  case 55:
#line 317 "simplangparser.yy"
    { (yyval.snode_list) = new list<ASTNode*>(); }
    break;

  case 56:
#line 319 "simplangparser.yy"
    { (yyvsp[(1) - (2)].snode_list)->push_back((yyvsp[(2) - (2)].snode)); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 57:
#line 323 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(VARB_T, (yyvsp[(2) - (4)].str)); (yyval.snode)->children = new list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(3) - (4)].snode)); }
    break;

  case 58:
#line 327 "simplangparser.yy"
    { (yyval.snode_list) = new list<ASTNode*>(); }
    break;

  case 59:
#line 329 "simplangparser.yy"
    { (yyvsp[(1) - (2)].snode_list)->push_back((yyvsp[(2) - (2)].snode)); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 60:
#line 333 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(SV_T, (yyvsp[(2) - (4)].str));  (yyval.snode)->children = new list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(3) - (4)].snode)); }
    break;

  case 61:
#line 336 "simplangparser.yy"
    { (yyval.snode_list) = new list<ASTNode*>(); }
    break;

  case 62:
#line 338 "simplangparser.yy"
    { (yyvsp[(1) - (2)].snode_list)->push_back((yyvsp[(2) - (2)].snode)); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 63:
#line 342 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(TERM_T, NULL); (yyval.snode)->children = new list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(1) - (1)].snode)); }
    break;

  case 64:
#line 344 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(QID_T, NULL); (yyval.snode)->children = new list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(1) - (1)].snode)); }
    break;

  case 65:
#line 346 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(LQID_T, NULL);
            (yyval.snode)->children = (yyvsp[(4) - (5)].snode_list);
            (yyval.snode)->children->push_front((yyvsp[(3) - (5)].snode));
        }
    break;

  case 66:
#line 352 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(LET_T, NULL);
            (yyval.snode)->children = new list<ASTNode*>();
            (yyvsp[(5) - (8)].snode_list)->push_front((yyvsp[(4) - (8)].snode));
            ASTNode* vbl = new ASTNode(VARBL_T, NULL);
            vbl->children = (yyvsp[(5) - (8)].snode_list);
            (yyval.snode)->children->push_back(vbl);
            (yyval.snode)->children->push_back((yyvsp[(7) - (8)].snode));
        }
    break;

  case 67:
#line 362 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(FORALL_T, NULL);
            (yyval.snode)->children = new list<ASTNode*>();
            (yyvsp[(5) - (8)].snode_list)->push_front((yyvsp[(4) - (8)].snode));
            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = (yyvsp[(5) - (8)].snode_list);
            (yyval.snode)->children->push_back(svl);
            (yyval.snode)->children->push_back((yyvsp[(7) - (8)].snode));
        }
    break;

  case 68:
#line 372 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(EXISTS_T, NULL);
            (yyval.snode)->children = new list<ASTNode*>();
            (yyvsp[(5) - (8)].snode_list)->push_front((yyvsp[(4) - (8)].snode));
            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = (yyvsp[(5) - (8)].snode_list);
            (yyval.snode)->children->push_back(svl);
            (yyval.snode)->children->push_back((yyvsp[(7) - (8)].snode));
        }
    break;

  case 69:
#line 382 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(BANG_T, NULL);
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(2) - (4)].snode));
            (yyvsp[(4) - (4)].snode_list)->push_front((yyvsp[(3) - (4)].snode));
            (yyval.snode)->children = (yyvsp[(4) - (4)].snode_list);
        }
    break;

  case 70:
#line 456 "simplangparser.yy"
    { (yyval.snode_list) = new list<ASTNode*>(); }
    break;

  case 71:
#line 458 "simplangparser.yy"
    { (yyvsp[(1) - (2)].snode_list)->push_back(new ASTNode(SYM_T, (yyvsp[(2) - (2)].str))); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 72:
#line 615 "simplangparser.yy"
    {
            if (strcmp((yyvsp[(1) - (1)].str), "true") == 0)
                (yyval.snode) = new ASTNode(BOOL_T, "true");
            else if (strcmp((yyvsp[(1) - (1)].str), "false") == 0)
                (yyval.snode) = new ASTNode(BOOL_T, "false");
            else {
                printf("Syntax error: expecting either 'true' or 'false', got '%s'\n", (yyvsp[(1) - (1)].str));
                YYERROR;
            }
        }
    break;

  case 73:
#line 628 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode));
        }
    break;

  case 74:
#line 634 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode));
        }
    break;

  case 75:
#line 640 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode));
        }
    break;

  case 76:
#line 646 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode));
        }
    break;

  case 77:
#line 652 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode));
        }
    break;

  case 78:
#line 658 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode));
        }
    break;

  case 79:
#line 664 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode));
        }
    break;

  case 80:
#line 670 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(STR_T, (yyvsp[(2) - (2)].str)));
        }
    break;

  case 81:
#line 676 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(STR_T, (yyvsp[(2) - (2)].str)));
        }
    break;

  case 82:
#line 682 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[(2) - (2)].str)));
        }
    break;

  case 83:
#line 688 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[(2) - (2)].str)));
        }
    break;

  case 84:
#line 694 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, NULL);
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(1) - (1)].snode));
        }
    break;

  case 85:
#line 702 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 86:
#line 704 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 87:
#line 706 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 88:
#line 708 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 89:
#line 710 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 90:
#line 712 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 91:
#line 714 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 92:
#line 716 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 93:
#line 718 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 94:
#line 720 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 95:
#line 722 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 96:
#line 724 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 97:
#line 726 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 98:
#line 728 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 99:
#line 730 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 100:
#line 732 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 101:
#line 734 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 102:
#line 736 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 103:
#line 738 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 104:
#line 740 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 105:
#line 742 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 106:
#line 744 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 107:
#line 746 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 108:
#line 748 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 109:
#line 750 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 110:
#line 752 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 111:
#line 754 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 112:
#line 756 "simplangparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 113:
#line 760 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 114:
#line 762 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 115:
#line 764 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 116:
#line 766 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 117:
#line 768 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 118:
#line 770 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 119:
#line 772 "simplangparser.yy"
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 120:
#line 774 "simplangparser.yy"
    {
            (yyval.snode) = new ASTNode(INFO_T, NULL);
            (yyval.snode)->children = new list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(GATTR_T, (yyvsp[(1) - (1)].str)));
        }
    break;


/* Line 1267 of yacc.c.  */
#line 2558 "simplangparser.cc"
      default: break;
    }
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;
  *++yylsp = yyloc;

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
      yyerror (&yylloc, context, YY_("syntax error"));
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
	    yyerror (&yylloc, context, yymsg);
	  }
	else
	  {
	    yyerror (&yylloc, context, YY_("syntax error"));
	    if (yysize != 0)
	      goto yyexhaustedlab;
	  }
      }
#endif
    }

  yyerror_range[0] = yylloc;

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
		      yytoken, &yylval, &yylloc, context);
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

  yyerror_range[0] = yylsp[1-yylen];
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

      yyerror_range[0] = *yylsp;
      yydestruct ("Error: popping",
		  yystos[yystate], yyvsp, yylsp, context);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  if (yyn == YYFINAL)
    YYACCEPT;

  *++yyvsp = yylval;

  yyerror_range[1] = yylloc;
  /* Using YYLLOC is tempting, but would change the location of
     the look-ahead.  YYLOC is available though.  */
  YYLLOC_DEFAULT (yyloc, (yyerror_range - 1), 2);
  *++yylsp = yyloc;

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
  yyerror (&yylloc, context, YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEOF && yychar != YYEMPTY)
     yydestruct ("Cleanup: discarding lookahead",
		 yytoken, &yylval, &yylloc, context);
  /* Do not reclaim the symbols of the rule which action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
		  yystos[*yyssp], yyvsp, yylsp, context);
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


#line 781 "simplangparser.yy"


//=======================================================================================
// Auxiliary Routines


