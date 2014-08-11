/* A Bison parser, made by GNU Bison 2.5.  */

/* Bison implementation for Yacc-like parsers in C
   
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
#define YYBISON_VERSION "2.5"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 1

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1

/* Using locations.  */
#define YYLSP_NEEDED 1

/* Substitute the variable and function names.  */
#define yyparse         smt2newparse
#define yylex           smt2newlex
#define yyerror         smt2newerror
#define yylval          smt2newlval
#define yychar          smt2newchar
#define yydebug         smt2newdebug
#define yynerrs         smt2newnerrs
#define yylloc          smt2newlloc

/* Copy the first part of user declarations.  */

/* Line 268 of yacc.c  */
#line 35 "smt2newparser.yy"

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


/* Line 268 of yacc.c  */
#line 110 "smt2newparser.cc"

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
     TK_WRSTATE = 287,
     TK_RDSTATE = 288,
     TK_NUM = 289,
     TK_SYM = 290,
     TK_KEY = 291,
     TK_STR = 292,
     TK_DEC = 293,
     TK_HEX = 294,
     TK_BIN = 295,
     KW_SORTS = 296,
     KW_FUNS = 297,
     KW_SORTSDESCRIPTION = 298,
     KW_FUNSDESCRIPTION = 299,
     KW_DEFINITION = 300,
     KW_NOTES = 301,
     KW_THEORIES = 302,
     KW_LANGUAGE = 303,
     KW_EXTENSIONS = 304,
     KW_VALUES = 305,
     KW_PRINTSUCCESS = 306,
     KW_EXPANDDEFINITIONS = 307,
     KW_INTERACTIVEMODE = 308,
     KW_PRODUCEPROOFS = 309,
     KW_PRODUCEUNSATCORES = 310,
     KW_PRODUCEMODELS = 311,
     KW_PRODUCEASSIGNMENTS = 312,
     KW_REGULAROUTPUTCHANNEL = 313,
     KW_DIAGNOSTICOUTPUTCHANNEL = 314,
     KW_RANDOMSEED = 315,
     KW_VERBOSITY = 316,
     KW_ERRORBEHAVIOR = 317,
     KW_NAME = 318,
     KW_NAMED = 319,
     KW_AUTHORS = 320,
     KW_VERSION = 321,
     KW_STATUS = 322,
     KW_REASONUNKNOWN = 323,
     KW_ALLSTATISTICS = 324
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
#define TK_WRSTATE 287
#define TK_RDSTATE 288
#define TK_NUM 289
#define TK_SYM 290
#define TK_KEY 291
#define TK_STR 292
#define TK_DEC 293
#define TK_HEX 294
#define TK_BIN 295
#define KW_SORTS 296
#define KW_FUNS 297
#define KW_SORTSDESCRIPTION 298
#define KW_FUNSDESCRIPTION 299
#define KW_DEFINITION 300
#define KW_NOTES 301
#define KW_THEORIES 302
#define KW_LANGUAGE 303
#define KW_EXTENSIONS 304
#define KW_VALUES 305
#define KW_PRINTSUCCESS 306
#define KW_EXPANDDEFINITIONS 307
#define KW_INTERACTIVEMODE 308
#define KW_PRODUCEPROOFS 309
#define KW_PRODUCEUNSATCORES 310
#define KW_PRODUCEMODELS 311
#define KW_PRODUCEASSIGNMENTS 312
#define KW_REGULAROUTPUTCHANNEL 313
#define KW_DIAGNOSTICOUTPUTCHANNEL 314
#define KW_RANDOMSEED 315
#define KW_VERBOSITY 316
#define KW_ERRORBEHAVIOR 317
#define KW_NAME 318
#define KW_NAMED 319
#define KW_AUTHORS 320
#define KW_VERSION 321
#define KW_STATUS 322
#define KW_REASONUNKNOWN 323
#define KW_ALLSTATISTICS 324




#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
{

/* Line 293 of yacc.c  */
#line 66 "smt2newparser.yy"

  char  *                      str;
  std::vector< std::string > * str_list;
  ASTNode *                    snode;
  std::list< ASTNode * > *     snode_list;



/* Line 293 of yacc.c  */
#line 293 "smt2newparser.cc"
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


/* Copy the second part of user declarations.  */


/* Line 343 of yacc.c  */
#line 318 "smt2newparser.cc"

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
YYID (int yyi)
#else
static int
YYID (yyi)
    int yyi;
#endif
{
  return yyi;
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
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
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
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
	     && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS && (defined __STDC__ || defined __C99__FUNC__ \
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
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
  YYLTYPE yyls_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE) + sizeof (YYLTYPE)) \
      + 2 * YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)				\
    do									\
      {									\
	YYSIZE_T yynewbytes;						\
	YYCOPY (&yyptr->Stack_alloc, Stack, yysize);			\
	Stack = &yyptr->Stack_alloc;					\
	yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
	yyptr += yynewbytes / sizeof (*yyptr);				\
      }									\
    while (YYID (0))

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
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
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  3
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   342

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  74
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  26
/* YYNRULES -- Number of rules.  */
#define YYNRULES  124
/* YYNRULES -- Number of states.  */
#define YYNSTATES  233

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   324

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    73,     2,     2,     2,     2,     2,     2,
      70,    71,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,    72,     2,     2,     2,     2,
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
      65,    66,    67,    68,    69
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     5,     6,     9,    14,    19,    24,    30,
      39,    48,    58,    63,    68,    73,    77,    81,    85,    89,
      94,    99,   103,   111,   115,   120,   125,   130,   134,   135,
     138,   140,   143,   145,   148,   150,   152,   156,   158,   164,
     166,   172,   175,   176,   178,   180,   182,   186,   187,   190,
     192,   194,   196,   198,   200,   203,   205,   207,   213,   214,
     217,   222,   223,   226,   231,   232,   235,   237,   239,   245,
     254,   263,   272,   279,   280,   283,   285,   288,   291,   294,
     297,   300,   303,   306,   309,   312,   315,   318,   320,   322,
     324,   326,   328,   330,   332,   334,   336,   338,   340,   342,
     344,   346,   348,   350,   352,   354,   356,   358,   360,   362,
     364,   366,   368,   370,   372,   374,   376,   378,   380,   382,
     384,   386,   388,   390,   392
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int8 yyrhs[] =
{
      75,     0,    -1,    76,    -1,    -1,    76,    77,    -1,    70,
      27,    35,    71,    -1,    70,    29,    97,    71,    -1,    70,
      28,    79,    71,    -1,    70,    13,    35,    34,    71,    -1,
      70,    15,    35,    70,    95,    71,    82,    71,    -1,    70,
      14,    35,    70,    83,    71,    82,    71,    -1,    70,    16,
      35,    70,    91,    71,    82,    94,    71,    -1,    70,    26,
      34,    71,    -1,    70,    25,    34,    71,    -1,    70,    11,
      94,    71,    -1,    70,    12,    71,    -1,    70,    18,    71,
      -1,    70,    22,    71,    -1,    70,    31,    71,    -1,    70,
      32,    37,    71,    -1,    70,    33,    37,    71,    -1,    70,
      23,    71,    -1,    70,    24,    70,    94,    93,    71,    71,
      -1,    70,    19,    71,    -1,    70,    21,    36,    71,    -1,
      70,    21,    98,    71,    -1,    70,    20,    99,    71,    -1,
      70,    17,    71,    -1,    -1,    78,    79,    -1,    36,    -1,
      36,    80,    -1,    98,    -1,    98,    80,    -1,    86,    -1,
      35,    -1,    70,    85,    71,    -1,    35,    -1,    70,    72,
      35,    87,    71,    -1,    81,    -1,    70,    81,    82,    83,
      71,    -1,    83,    82,    -1,    -1,    86,    -1,    35,    -1,
      36,    -1,    70,    85,    71,    -1,    -1,    85,    84,    -1,
      34,    -1,    38,    -1,    39,    -1,    40,    -1,    37,    -1,
      87,    34,    -1,    34,    -1,    81,    -1,    70,     3,    81,
      82,    71,    -1,    -1,    89,    90,    -1,    70,    35,    94,
      71,    -1,    -1,    91,    92,    -1,    70,    35,    82,    71,
      -1,    -1,    93,    94,    -1,    86,    -1,    88,    -1,    70,
      88,    94,    93,    71,    -1,    70,     7,    70,    90,    89,
      71,    94,    71,    -1,    70,     6,    70,    92,    91,    71,
      94,    71,    -1,    70,     5,    70,    92,    91,    71,    94,
      71,    -1,    70,    73,    94,    79,    78,    71,    -1,    -1,
      95,    35,    -1,    35,    -1,    51,    96,    -1,    52,    96,
      -1,    53,    96,    -1,    54,    96,    -1,    55,    96,    -1,
      56,    96,    -1,    57,    96,    -1,    58,    37,    -1,    59,
      37,    -1,    60,    34,    -1,    61,    34,    -1,    79,    -1,
      41,    -1,    42,    -1,    43,    -1,    44,    -1,    45,    -1,
      50,    -1,    46,    -1,    47,    -1,    48,    -1,    49,    -1,
      51,    -1,    52,    -1,    53,    -1,    54,    -1,    55,    -1,
      56,    -1,    57,    -1,    58,    -1,    59,    -1,    60,    -1,
      61,    -1,    62,    -1,    63,    -1,    64,    -1,    65,    -1,
      66,    -1,    67,    -1,    68,    -1,    69,    -1,    62,    -1,
      63,    -1,    65,    -1,    66,    -1,    67,    -1,    68,    -1,
      69,    -1,    36,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,    95,    95,    99,   100,   104,   110,   116,   122,   129,
     142,   154,   167,   173,   179,   185,   189,   193,   197,   201,
     207,   213,   217,   223,   227,   233,   239,   245,   250,   251,
     255,   257,   259,   261,   265,   267,   271,   278,   280,   284,
     286,   294,   297,   300,   306,   310,   314,   322,   325,   332,
     334,   336,   338,   340,   344,   346,   350,   352,   362,   363,
     367,   372,   373,   377,   381,   382,   386,   388,   390,   397,
     407,   417,   427,   504,   505,   662,   675,   681,   687,   693,
     699,   705,   711,   717,   723,   729,   735,   741,   749,   751,
     753,   755,   757,   759,   761,   763,   765,   767,   769,   771,
     773,   775,   777,   779,   781,   783,   785,   787,   789,   791,
     793,   795,   797,   799,   801,   803,   805,   809,   811,   813,
     815,   817,   819,   821,   823
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
  "TK_SETOPTION", "TK_THEORY", "TK_GETITPS", "TK_WRSTATE", "TK_RDSTATE",
  "TK_NUM", "TK_SYM", "TK_KEY", "TK_STR", "TK_DEC", "TK_HEX", "TK_BIN",
  "KW_SORTS", "KW_FUNS", "KW_SORTSDESCRIPTION", "KW_FUNSDESCRIPTION",
  "KW_DEFINITION", "KW_NOTES", "KW_THEORIES", "KW_LANGUAGE",
  "KW_EXTENSIONS", "KW_VALUES", "KW_PRINTSUCCESS", "KW_EXPANDDEFINITIONS",
  "KW_INTERACTIVEMODE", "KW_PRODUCEPROOFS", "KW_PRODUCEUNSATCORES",
  "KW_PRODUCEMODELS", "KW_PRODUCEASSIGNMENTS", "KW_REGULAROUTPUTCHANNEL",
  "KW_DIAGNOSTICOUTPUTCHANNEL", "KW_RANDOMSEED", "KW_VERBOSITY",
  "KW_ERRORBEHAVIOR", "KW_NAME", "KW_NAMED", "KW_AUTHORS", "KW_VERSION",
  "KW_STATUS", "KW_REASONUNKNOWN", "KW_ALLSTATISTICS", "'('", "')'", "'_'",
  "'!'", "$accept", "script", "command_list", "command", "attribute_list",
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
     315,   316,   317,   318,   319,   320,   321,   322,   323,   324,
      40,    41,    95,    33
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    74,    75,    76,    76,    77,    77,    77,    77,    77,
      77,    77,    77,    77,    77,    77,    77,    77,    77,    77,
      77,    77,    77,    77,    77,    77,    77,    77,    78,    78,
      79,    79,    79,    79,    80,    80,    80,    81,    81,    82,
      82,    83,    83,    84,    84,    84,    84,    85,    85,    86,
      86,    86,    86,    86,    87,    87,    88,    88,    89,    89,
      90,    91,    91,    92,    93,    93,    94,    94,    94,    94,
      94,    94,    94,    95,    95,    96,    97,    97,    97,    97,
      97,    97,    97,    97,    97,    97,    97,    97,    98,    98,
      98,    98,    98,    98,    98,    98,    98,    98,    98,    98,
      98,    98,    98,    98,    98,    98,    98,    98,    98,    98,
      98,    98,    98,    98,    98,    98,    98,    99,    99,    99,
      99,    99,    99,    99,    99
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     0,     2,     4,     4,     4,     5,     8,
       8,     9,     4,     4,     4,     3,     3,     3,     3,     4,
       4,     3,     7,     3,     4,     4,     4,     3,     0,     2,
       1,     2,     1,     2,     1,     1,     3,     1,     5,     1,
       5,     2,     0,     1,     1,     1,     3,     0,     2,     1,
       1,     1,     1,     1,     2,     1,     1,     5,     0,     2,
       4,     0,     2,     4,     0,     2,     1,     1,     5,     8,
       8,     8,     6,     0,     2,     1,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1
};

/* YYDEFACT[STATE-NAME] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       3,     0,     2,     1,     0,     4,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    49,    37,
      53,    50,    51,    52,     0,    56,    66,    67,     0,    15,
       0,     0,     0,     0,    27,    16,    23,   124,   117,   118,
     119,   120,   121,   122,   123,     0,     0,    88,    89,    90,
      91,    92,    94,    95,    96,    97,    93,    98,    99,   100,
     101,   102,   103,   104,   105,   106,   107,   108,   109,   110,
     111,   112,   113,   114,   115,   116,     0,    17,    21,     0,
       0,     0,     0,    30,     0,    32,    98,    99,   100,   101,
     102,   103,   104,   105,   106,   107,   108,    87,     0,    18,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      14,     0,    42,    73,    61,    26,    24,    25,    64,    13,
      12,     5,    35,    47,    31,    34,     7,    33,    75,    76,
      77,    78,    79,    80,    81,    82,    83,    84,    85,    86,
       6,    19,    20,     0,     0,     0,     0,     0,     0,     0,
      64,     8,     0,     0,     0,     0,     0,     0,    39,     0,
       0,    61,    61,     0,    58,    55,     0,    28,     0,     0,
      41,    74,     0,     0,    62,     0,    65,    44,    45,    47,
      36,    48,    43,     0,    57,     0,     0,     0,     0,     0,
      54,    38,     0,    68,     0,     0,     0,    22,     0,    42,
       0,     0,     0,     0,     0,    59,    72,    29,    10,     9,
       0,    46,     0,    63,     0,     0,    60,     0,    11,    40,
      71,    70,    69
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     1,     2,     5,   202,    94,   134,    35,   180,   162,
     191,   166,    36,   176,    37,   199,   174,   164,   184,   165,
     186,   163,   139,   108,    95,    55
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -150
static const yytype_int16 yypact[] =
{
    -150,    37,   -19,  -150,   296,  -150,     1,   -13,    44,    47,
      49,    53,    26,    32,    40,   270,   168,    57,    58,    38,
      96,    98,    99,   202,   236,    60,   130,   132,  -150,  -150,
    -150,  -150,  -150,  -150,     8,  -150,  -150,  -150,    64,  -150,
     136,   101,   102,   103,  -150,  -150,  -150,  -150,  -150,  -150,
    -150,  -150,  -150,  -150,  -150,   104,   105,  -150,  -150,  -150,
    -150,  -150,  -150,  -150,  -150,  -150,  -150,  -150,  -150,  -150,
    -150,  -150,  -150,  -150,  -150,  -150,  -150,  -150,  -150,  -150,
    -150,  -150,  -150,  -150,  -150,  -150,   106,  -150,  -150,     1,
     107,   109,   110,    67,   111,    67,   139,   139,   139,   139,
     139,   139,   139,   146,   147,   151,   152,  -150,   116,  -150,
     117,   118,   -28,   120,   121,   123,     0,   159,     1,     1,
    -150,   124,  -150,  -150,  -150,  -150,  -150,  -150,  -150,  -150,
    -150,  -150,  -150,  -150,  -150,  -150,  -150,  -150,  -150,  -150,
    -150,  -150,  -150,  -150,  -150,  -150,  -150,  -150,  -150,  -150,
    -150,  -150,  -150,   125,    22,   126,   126,   128,   165,   202,
    -150,  -150,    15,    29,   -62,    28,   -18,   -25,  -150,   131,
     166,  -150,  -150,   172,  -150,  -150,   -22,  -150,    56,    22,
    -150,  -150,    22,    22,  -150,   169,  -150,  -150,  -150,  -150,
    -150,  -150,  -150,    22,  -150,    22,   -39,   -16,     1,    -1,
    -150,  -150,    97,  -150,   170,   171,     1,  -150,   -11,  -150,
     203,     1,     1,   204,     1,  -150,  -150,  -150,  -150,  -150,
     205,  -150,    39,  -150,   255,   259,  -150,   260,  -150,  -150,
    -150,  -150,  -150
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -150,  -150,  -150,  -150,  -150,   -23,   108,  -106,  -149,    30,
    -150,    84,   -91,  -150,   300,  -150,   141,   -57,   -31,   181,
      -6,  -150,    21,  -150,   326,  -150
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -1
static const yytype_uint8 yytable[] =
{
      38,   107,   135,   112,   135,   169,   154,    29,   170,   183,
      29,   112,   200,   113,   114,   115,    28,   187,   188,    30,
      31,    32,    33,    28,   187,   188,    30,    31,    32,    33,
     204,   170,   211,   205,   206,    28,    29,     3,    30,    31,
      32,    33,   153,    29,   209,   153,   210,   117,   168,   201,
      29,     4,   189,   190,   170,   212,   168,    29,    39,   189,
     221,   193,    28,    29,   181,    30,    31,    32,    33,   173,
     214,    34,   117,   168,    29,   192,   168,   168,   116,    40,
     117,   118,    41,   128,    42,   167,   179,   168,    43,   168,
      28,    29,   167,    30,    31,    32,    33,    44,    34,   185,
     182,    28,   132,    45,    30,    31,    32,    33,    89,   167,
     229,    46,   159,   160,   196,   197,   168,   192,   140,   141,
     142,   143,   144,   145,   171,   172,    34,   203,    87,    88,
      90,   109,    91,    93,    92,   120,   177,   133,    57,    58,
      59,    60,    61,    62,    63,    64,    65,    66,    67,    68,
      69,    70,    71,    72,    73,    74,    75,    76,    77,    78,
      79,    80,    81,    82,    83,    84,    85,   110,   216,   111,
     121,   122,   123,   124,   138,   125,   126,   127,   129,   217,
     130,   131,   136,   146,   147,   148,   149,   150,   151,   152,
     155,   156,   213,   157,   158,   161,   170,   117,   173,   175,
     220,   195,   194,   137,    56,   224,   225,   198,   227,    57,
      58,    59,    60,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    82,    83,    84,    85,    93,   222,
     207,   218,   219,    57,    58,    59,    60,    61,    62,    63,
      64,    65,    66,    67,    68,    69,    70,    71,    72,    73,
      74,    75,    76,    77,    78,    79,    80,    81,    82,    83,
      84,    85,    93,   208,   223,   226,   228,    57,    58,    59,
      60,    61,    62,    63,    64,    65,    66,    96,    97,    98,
      99,   100,   101,   102,   103,   104,   105,   106,    78,    79,
      80,    81,    82,    83,    84,    85,    47,     6,     7,     8,
       9,    10,    11,    12,    13,    14,    15,    16,    17,    18,
      19,    20,    21,    22,    23,    24,   230,    25,    26,    27,
     231,   232,    48,    49,   119,    50,    51,    52,    53,    54,
     215,   178,    86
};

#define yypact_value_is_default(yystate) \
  ((yystate) == (-150))

#define yytable_value_is_error(yytable_value) \
  YYID (0)

static const yytype_uint8 yycheck[] =
{
       6,    24,    93,     3,    95,   154,   112,    35,    70,    71,
      35,     3,    34,     5,     6,     7,    34,    35,    36,    37,
      38,    39,    40,    34,    35,    36,    37,    38,    39,    40,
     179,    70,    71,   182,   183,    34,    35,     0,    37,    38,
      39,    40,    70,    35,   193,    70,   195,    72,   154,    71,
      35,    70,    70,    71,    70,    71,   162,    35,    71,    70,
      71,   167,    34,    35,    35,    37,    38,    39,    40,    70,
      71,    70,    72,   179,    35,   166,   182,   183,    70,    35,
      72,    73,    35,    89,    35,    70,    71,   193,    35,   195,
      34,    35,    70,    37,    38,    39,    40,    71,    70,    71,
      71,    34,    35,    71,    37,    38,    39,    40,    70,    70,
      71,    71,   118,   119,   171,   172,   222,   208,    97,    98,
      99,   100,   101,   102,   155,   156,    70,    71,    71,    71,
      34,    71,    34,    36,    35,    71,   159,    70,    41,    42,
      43,    44,    45,    46,    47,    48,    49,    50,    51,    52,
      53,    54,    55,    56,    57,    58,    59,    60,    61,    62,
      63,    64,    65,    66,    67,    68,    69,    37,    71,    37,
      34,    70,    70,    70,    35,    71,    71,    71,    71,   202,
      71,    71,    71,    37,    37,    34,    34,    71,    71,    71,
      70,    70,   198,    70,    35,    71,    70,    72,    70,    34,
     206,    35,    71,    95,    36,   211,   212,    35,   214,    41,
      42,    43,    44,    45,    46,    47,    48,    49,    50,    51,
      52,    53,    54,    55,    56,    57,    58,    59,    60,    61,
      62,    63,    64,    65,    66,    67,    68,    69,    36,   209,
      71,    71,    71,    41,    42,    43,    44,    45,    46,    47,
      48,    49,    50,    51,    52,    53,    54,    55,    56,    57,
      58,    59,    60,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    36,   189,    71,    71,    71,    41,    42,    43,
      44,    45,    46,    47,    48,    49,    50,    51,    52,    53,
      54,    55,    56,    57,    58,    59,    60,    61,    62,    63,
      64,    65,    66,    67,    68,    69,    36,    11,    12,    13,
      14,    15,    16,    17,    18,    19,    20,    21,    22,    23,
      24,    25,    26,    27,    28,    29,    71,    31,    32,    33,
      71,    71,    62,    63,    34,    65,    66,    67,    68,    69,
     199,   160,    16
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    75,    76,     0,    70,    77,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    31,    32,    33,    34,    35,
      37,    38,    39,    40,    70,    81,    86,    88,    94,    71,
      35,    35,    35,    35,    71,    71,    71,    36,    62,    63,
      65,    66,    67,    68,    69,    99,    36,    41,    42,    43,
      44,    45,    46,    47,    48,    49,    50,    51,    52,    53,
      54,    55,    56,    57,    58,    59,    60,    61,    62,    63,
      64,    65,    66,    67,    68,    69,    98,    71,    71,    70,
      34,    34,    35,    36,    79,    98,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    79,    97,    71,
      37,    37,     3,     5,     6,     7,    70,    72,    73,    88,
      71,    34,    70,    70,    70,    71,    71,    71,    94,    71,
      71,    71,    35,    70,    80,    86,    71,    80,    35,    96,
      96,    96,    96,    96,    96,    96,    37,    37,    34,    34,
      71,    71,    71,    70,    81,    70,    70,    70,    35,    94,
      94,    71,    83,    95,    91,    93,    85,    70,    81,    82,
      70,    92,    92,    70,    90,    34,    87,    79,    93,    71,
      82,    35,    71,    71,    92,    71,    94,    35,    36,    70,
      71,    84,    86,    81,    71,    35,    91,    91,    35,    89,
      34,    71,    78,    71,    82,    82,    82,    71,    85,    82,
      82,    71,    71,    94,    71,    90,    71,    79,    71,    71,
      94,    71,    83,    71,    94,    94,    71,    94,    71,    71,
      71,    71,    71
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
   Once GCC version 2 has supplanted version 1, this can go.  However,
   YYFAIL appears to be in use.  Nevertheless, it is formally deprecated
   in Bison 2.4.2's NEWS entry, where a plan to phase it out is
   discussed.  */

#define YYFAIL		goto yyerrlab
#if defined YYFAIL
  /* This is here to suppress warnings from the GCC cpp's
     -Wunused-macros.  Normally we don't worry about that warning, but
     some users do, and we want to make it easy for users to remove
     YYFAIL uses, which will produce warnings from Bison 2.5.  */
#endif

#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)					\
do								\
  if (yychar == YYEMPTY && yylen == 1)				\
    {								\
      yychar = (Token);						\
      yylval = (Value);						\
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
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, Smt2newContext* context)
#else
static void
yy_symbol_value_print (yyoutput, yytype, yyvaluep, yylocationp, context)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
    YYLTYPE const * const yylocationp;
    Smt2newContext* context;
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
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, Smt2newContext* context)
#else
static void
yy_symbol_print (yyoutput, yytype, yyvaluep, yylocationp, context)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
    YYLTYPE const * const yylocationp;
    Smt2newContext* context;
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
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
#else
static void
yy_stack_print (yybottom, yytop)
    yytype_int16 *yybottom;
    yytype_int16 *yytop;
#endif
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
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
yy_reduce_print (YYSTYPE *yyvsp, YYLTYPE *yylsp, int yyrule, Smt2newContext* context)
#else
static void
yy_reduce_print (yyvsp, yylsp, yyrule, context)
    YYSTYPE *yyvsp;
    YYLTYPE *yylsp;
    int yyrule;
    Smt2newContext* context;
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
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr, yyrhs[yyprhs[yyrule] + yyi],
		       &(yyvsp[(yyi + 1) - (yynrhs)])
		       , &(yylsp[(yyi + 1) - (yynrhs)])		       , context);
      YYFPRINTF (stderr, "\n");
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

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (0, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  YYSIZE_T yysize1;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = 0;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - Assume YYFAIL is not used.  It's too flawed to consider.  See
       <http://lists.gnu.org/archive/html/bison-patches/2009-12/msg00024.html>
       for details.  YYERROR is fine as it does not invoke this
       function.
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                yysize1 = yysize + yytnamerr (0, yytname[yyx]);
                if (! (yysize <= yysize1
                       && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                  return 2;
                yysize = yysize1;
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  yysize1 = yysize + yystrlen (yyformat);
  if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
    return 2;
  yysize = yysize1;

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, YYLTYPE *yylocationp, Smt2newContext* context)
#else
static void
yydestruct (yymsg, yytype, yyvaluep, yylocationp, context)
    const char *yymsg;
    int yytype;
    YYSTYPE *yyvaluep;
    YYLTYPE *yylocationp;
    Smt2newContext* context;
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
int yyparse (Smt2newContext* context);
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
yyparse (Smt2newContext* context)
#else
int
yyparse (context)
    Smt2newContext* context;
#endif
#endif
{
/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;

/* Location data for the lookahead symbol.  */
YYLTYPE yylloc;

    /* Number of syntax errors so far.  */
    int yynerrs;

    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       `yyss': related to states.
       `yyvs': related to semantic values.
       `yyls': related to locations.

       Refer to the stacks thru separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    /* The location stack.  */
    YYLTYPE yylsa[YYINITDEPTH];
    YYLTYPE *yyls;
    YYLTYPE *yylsp;

    /* The locations where the error started and ended.  */
    YYLTYPE yyerror_range[3];

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;
  YYLTYPE yyloc;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N), yylsp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yytoken = 0;
  yyss = yyssa;
  yyvs = yyvsa;
  yyls = yylsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */

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
  yylloc.first_column = yylloc.last_column = 1;
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
	YYSTACK_RELOCATE (yyss_alloc, yyss);
	YYSTACK_RELOCATE (yyvs_alloc, yyvs);
	YYSTACK_RELOCATE (yyls_alloc, yyls);
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

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
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
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
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

/* Line 1806 of yacc.c  */
#line 95 "smt2newparser.yy"
    { ASTNode *n = new ASTNode(CMDL_T, "main-script"); n->children = (yyvsp[(1) - (1)].snode_list); context->insertRoot(n); }
    break;

  case 3:

/* Line 1806 of yacc.c  */
#line 99 "smt2newparser.yy"
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
    break;

  case 4:

/* Line 1806 of yacc.c  */
#line 101 "smt2newparser.yy"
    { (*(yyvsp[(1) - (2)].snode_list)).push_back((yyvsp[(2) - (2)].snode)); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 5:

/* Line 1806 of yacc.c  */
#line 105 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[(3) - (4)].str)));
        }
    break;

  case 6:

/* Line 1806 of yacc.c  */
#line 111 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(3) - (4)].snode));
        }
    break;

  case 7:

/* Line 1806 of yacc.c  */
#line 117 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(3) - (4)].snode));
        }
    break;

  case 8:

/* Line 1806 of yacc.c  */
#line 123 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (5)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[(3) - (5)].str)));
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[(4) - (5)].str)));
        }
    break;

  case 9:

/* Line 1806 of yacc.c  */
#line 130 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (8)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[(3) - (8)].str)));

            ASTNode* syml = new ASTNode(SYML_T, NULL);
            syml->children = (yyvsp[(5) - (8)].snode_list);
            (yyval.snode)->children->push_back(syml);

            (yyval.snode)->children->push_back((yyvsp[(7) - (8)].snode));
        }
    break;

  case 10:

/* Line 1806 of yacc.c  */
#line 143 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (8)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[(3) - (8)].str)));

            ASTNode* sortl = new ASTNode(SORTL_T, NULL);
            sortl->children = (yyvsp[(5) - (8)].snode_list);
            (yyval.snode)->children->push_back(sortl);

            (yyval.snode)->children->push_back((yyvsp[(7) - (8)].snode));
        }
    break;

  case 11:

/* Line 1806 of yacc.c  */
#line 155 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (9)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[(3) - (9)].str)));

            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = (yyvsp[(5) - (9)].snode_list);
            (yyval.snode)->children->push_back(svl);

            (yyval.snode)->children->push_back((yyvsp[(7) - (9)].snode));
            (yyval.snode)->children->push_back((yyvsp[(8) - (9)].snode));
        }
    break;

  case 12:

/* Line 1806 of yacc.c  */
#line 168 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[(3) - (4)].str)));
        }
    break;

  case 13:

/* Line 1806 of yacc.c  */
#line 174 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[(3) - (4)].str)));
        }
    break;

  case 14:

/* Line 1806 of yacc.c  */
#line 180 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(3) - (4)].snode));
        }
    break;

  case 15:

/* Line 1806 of yacc.c  */
#line 186 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (3)].str));
        }
    break;

  case 16:

/* Line 1806 of yacc.c  */
#line 190 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (3)].str));
        }
    break;

  case 17:

/* Line 1806 of yacc.c  */
#line 194 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (3)].str));
        }
    break;

  case 18:

/* Line 1806 of yacc.c  */
#line 198 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (3)].str));
        }
    break;

  case 19:

/* Line 1806 of yacc.c  */
#line 202 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[(3) - (4)].str)));
        }
    break;

  case 20:

/* Line 1806 of yacc.c  */
#line 208 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[(3) - (4)].str)));
        }
    break;

  case 21:

/* Line 1806 of yacc.c  */
#line 214 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (3)].str));
        }
    break;

  case 22:

/* Line 1806 of yacc.c  */
#line 218 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (7)].str));
            (yyval.snode)->children = (yyvsp[(5) - (7)].snode_list);
            (yyval.snode)->children->push_front((yyvsp[(4) - (7)].snode));
        }
    break;

  case 23:

/* Line 1806 of yacc.c  */
#line 224 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (3)].str));
        }
    break;

  case 24:

/* Line 1806 of yacc.c  */
#line 228 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[(3) - (4)].str)));
        }
    break;

  case 25:

/* Line 1806 of yacc.c  */
#line 234 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(PATTR_T, (yyvsp[(3) - (4)].str)));
        }
    break;

  case 26:

/* Line 1806 of yacc.c  */
#line 240 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (4)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(3) - (4)].snode));
        }
    break;

  case 27:

/* Line 1806 of yacc.c  */
#line 246 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(CMD_T, (yyvsp[(2) - (3)].str)); }
    break;

  case 28:

/* Line 1806 of yacc.c  */
#line 250 "smt2newparser.yy"
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
    break;

  case 29:

/* Line 1806 of yacc.c  */
#line 252 "smt2newparser.yy"
    { (yyvsp[(1) - (2)].snode_list)->push_back((yyvsp[(2) - (2)].snode)); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 30:

/* Line 1806 of yacc.c  */
#line 256 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(UATTR_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 31:

/* Line 1806 of yacc.c  */
#line 258 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(UATTR_T, (yyvsp[(1) - (2)].str)); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode)); }
    break;

  case 32:

/* Line 1806 of yacc.c  */
#line 260 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(PATTR_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 33:

/* Line 1806 of yacc.c  */
#line 262 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(PATTR_T, (yyvsp[(1) - (2)].str)); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode)); }
    break;

  case 34:

/* Line 1806 of yacc.c  */
#line 266 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(SPECC_T, NULL); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(1) - (1)].snode)); }
    break;

  case 35:

/* Line 1806 of yacc.c  */
#line 268 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(SYM_T, (yyvsp[(1) - (1)].str));
        }
    break;

  case 36:

/* Line 1806 of yacc.c  */
#line 272 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(SEXPRL_T, NULL);
            (yyval.snode)->children = (yyvsp[(2) - (3)].snode_list);
        }
    break;

  case 37:

/* Line 1806 of yacc.c  */
#line 279 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(SYM_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 38:

/* Line 1806 of yacc.c  */
#line 281 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(SYM_T, (yyvsp[(3) - (5)].str)); (yyval.snode)->children = (yyvsp[(4) - (5)].snode_list); }
    break;

  case 39:

/* Line 1806 of yacc.c  */
#line 285 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(ID_T, NULL); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(1) - (1)].snode)); }
    break;

  case 40:

/* Line 1806 of yacc.c  */
#line 287 "smt2newparser.yy"
    {
        (yyval.snode) = new ASTNode(LID_T, NULL);
        (yyval.snode)->children = (yyvsp[(4) - (5)].snode_list);
        (yyval.snode)->children->push_front((yyvsp[(3) - (5)].snode));
      }
    break;

  case 41:

/* Line 1806 of yacc.c  */
#line 295 "smt2newparser.yy"
    { (yyvsp[(1) - (2)].snode_list)->push_back((yyvsp[(2) - (2)].snode)); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 42:

/* Line 1806 of yacc.c  */
#line 297 "smt2newparser.yy"
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
    break;

  case 43:

/* Line 1806 of yacc.c  */
#line 301 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(SPECC_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(1) - (1)].snode));
        }
    break;

  case 44:

/* Line 1806 of yacc.c  */
#line 307 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(SYM_T, (yyvsp[(1) - (1)].str));
        }
    break;

  case 45:

/* Line 1806 of yacc.c  */
#line 311 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(UATTR_T, (yyvsp[(1) - (1)].str));
        }
    break;

  case 46:

/* Line 1806 of yacc.c  */
#line 315 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(SEXPRL_T, NULL);
            (yyval.snode)->children = (yyvsp[(2) - (3)].snode_list);
        }
    break;

  case 47:

/* Line 1806 of yacc.c  */
#line 322 "smt2newparser.yy"
    {
            (yyval.snode_list) = new std::list<ASTNode*>();
        }
    break;

  case 48:

/* Line 1806 of yacc.c  */
#line 326 "smt2newparser.yy"
    {
            (yyvsp[(1) - (2)].snode_list)->push_back((yyvsp[(2) - (2)].snode));
            (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list);
        }
    break;

  case 49:

/* Line 1806 of yacc.c  */
#line 333 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(NUM_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 50:

/* Line 1806 of yacc.c  */
#line 335 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(DEC_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 51:

/* Line 1806 of yacc.c  */
#line 337 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(HEX_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 52:

/* Line 1806 of yacc.c  */
#line 339 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(BIN_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 53:

/* Line 1806 of yacc.c  */
#line 341 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(STR_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 54:

/* Line 1806 of yacc.c  */
#line 345 "smt2newparser.yy"
    { (yyvsp[(1) - (2)].snode_list)->push_back(new ASTNode(NUM_T, (yyvsp[(2) - (2)].str))); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 55:

/* Line 1806 of yacc.c  */
#line 347 "smt2newparser.yy"
    { (yyval.snode_list) = new std::list<ASTNode*>(); (yyval.snode_list)->push_back(new ASTNode(NUM_T, (yyvsp[(1) - (1)].str))); }
    break;

  case 56:

/* Line 1806 of yacc.c  */
#line 351 "smt2newparser.yy"
    { (yyval.snode) = (yyvsp[(1) - (1)].snode); }
    break;

  case 57:

/* Line 1806 of yacc.c  */
#line 353 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(AS_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(3) - (5)].snode));
            (yyval.snode)->children->push_back((yyvsp[(4) - (5)].snode));
        }
    break;

  case 58:

/* Line 1806 of yacc.c  */
#line 362 "smt2newparser.yy"
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
    break;

  case 59:

/* Line 1806 of yacc.c  */
#line 364 "smt2newparser.yy"
    { (yyvsp[(1) - (2)].snode_list)->push_back((yyvsp[(2) - (2)].snode)); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 60:

/* Line 1806 of yacc.c  */
#line 368 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(VARB_T, (yyvsp[(2) - (4)].str)); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(3) - (4)].snode)); }
    break;

  case 61:

/* Line 1806 of yacc.c  */
#line 372 "smt2newparser.yy"
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
    break;

  case 62:

/* Line 1806 of yacc.c  */
#line 374 "smt2newparser.yy"
    { (yyvsp[(1) - (2)].snode_list)->push_back((yyvsp[(2) - (2)].snode)); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 63:

/* Line 1806 of yacc.c  */
#line 378 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(SV_T, (yyvsp[(2) - (4)].str));  (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(3) - (4)].snode)); }
    break;

  case 64:

/* Line 1806 of yacc.c  */
#line 381 "smt2newparser.yy"
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
    break;

  case 65:

/* Line 1806 of yacc.c  */
#line 383 "smt2newparser.yy"
    { (yyvsp[(1) - (2)].snode_list)->push_back((yyvsp[(2) - (2)].snode)); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 66:

/* Line 1806 of yacc.c  */
#line 387 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(TERM_T, NULL); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(1) - (1)].snode)); }
    break;

  case 67:

/* Line 1806 of yacc.c  */
#line 389 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(QID_T, NULL); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[(1) - (1)].snode)); }
    break;

  case 68:

/* Line 1806 of yacc.c  */
#line 391 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(LQID_T, NULL);
            (yyval.snode)->children = (yyvsp[(4) - (5)].snode_list);
            (yyval.snode)->children->push_front((yyvsp[(3) - (5)].snode));
            (yyval.snode)->children->push_front((yyvsp[(2) - (5)].snode));
        }
    break;

  case 69:

/* Line 1806 of yacc.c  */
#line 398 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(LET_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyvsp[(5) - (8)].snode_list)->push_front((yyvsp[(4) - (8)].snode));
            ASTNode* vbl = new ASTNode(VARBL_T, NULL);
            vbl->children = (yyvsp[(5) - (8)].snode_list);
            (yyval.snode)->children->push_back(vbl);
            (yyval.snode)->children->push_back((yyvsp[(7) - (8)].snode));
        }
    break;

  case 70:

/* Line 1806 of yacc.c  */
#line 408 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(FORALL_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyvsp[(5) - (8)].snode_list)->push_front((yyvsp[(4) - (8)].snode));
            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = (yyvsp[(5) - (8)].snode_list);
            (yyval.snode)->children->push_back(svl);
            (yyval.snode)->children->push_back((yyvsp[(7) - (8)].snode));
        }
    break;

  case 71:

/* Line 1806 of yacc.c  */
#line 418 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(EXISTS_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyvsp[(5) - (8)].snode_list)->push_front((yyvsp[(4) - (8)].snode));
            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = (yyvsp[(5) - (8)].snode_list);
            (yyval.snode)->children->push_back(svl);
            (yyval.snode)->children->push_back((yyvsp[(7) - (8)].snode));
        }
    break;

  case 72:

/* Line 1806 of yacc.c  */
#line 428 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(BANG_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_front((yyvsp[(3) - (6)].snode));
            ASTNode *atrs = new ASTNode(GATTRL_T, NULL);
            (yyvsp[(5) - (6)].snode_list)->push_front((yyvsp[(4) - (6)].snode));
            atrs->children = (yyvsp[(5) - (6)].snode_list);
            (yyval.snode)->children->push_back(atrs);
        }
    break;

  case 73:

/* Line 1806 of yacc.c  */
#line 504 "smt2newparser.yy"
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
    break;

  case 74:

/* Line 1806 of yacc.c  */
#line 506 "smt2newparser.yy"
    { (yyvsp[(1) - (2)].snode_list)->push_back(new ASTNode(SYM_T, (yyvsp[(2) - (2)].str))); (yyval.snode_list) = (yyvsp[(1) - (2)].snode_list); }
    break;

  case 75:

/* Line 1806 of yacc.c  */
#line 663 "smt2newparser.yy"
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

  case 76:

/* Line 1806 of yacc.c  */
#line 676 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode));
        }
    break;

  case 77:

/* Line 1806 of yacc.c  */
#line 682 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode));
        }
    break;

  case 78:

/* Line 1806 of yacc.c  */
#line 688 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode));
        }
    break;

  case 79:

/* Line 1806 of yacc.c  */
#line 694 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode));
        }
    break;

  case 80:

/* Line 1806 of yacc.c  */
#line 700 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode));
        }
    break;

  case 81:

/* Line 1806 of yacc.c  */
#line 706 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode));
        }
    break;

  case 82:

/* Line 1806 of yacc.c  */
#line 712 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(2) - (2)].snode));
        }
    break;

  case 83:

/* Line 1806 of yacc.c  */
#line 718 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(STR_T, (yyvsp[(2) - (2)].str)));
        }
    break;

  case 84:

/* Line 1806 of yacc.c  */
#line 724 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(STR_T, (yyvsp[(2) - (2)].str)));
        }
    break;

  case 85:

/* Line 1806 of yacc.c  */
#line 730 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[(2) - (2)].str)));
        }
    break;

  case 86:

/* Line 1806 of yacc.c  */
#line 736 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[(1) - (2)].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[(2) - (2)].str)));
        }
    break;

  case 87:

/* Line 1806 of yacc.c  */
#line 742 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(OPTION_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[(1) - (1)].snode));
        }
    break;

  case 88:

/* Line 1806 of yacc.c  */
#line 750 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 89:

/* Line 1806 of yacc.c  */
#line 752 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 90:

/* Line 1806 of yacc.c  */
#line 754 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 91:

/* Line 1806 of yacc.c  */
#line 756 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 92:

/* Line 1806 of yacc.c  */
#line 758 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 93:

/* Line 1806 of yacc.c  */
#line 760 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 94:

/* Line 1806 of yacc.c  */
#line 762 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 95:

/* Line 1806 of yacc.c  */
#line 764 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 96:

/* Line 1806 of yacc.c  */
#line 766 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 97:

/* Line 1806 of yacc.c  */
#line 768 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 98:

/* Line 1806 of yacc.c  */
#line 770 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 99:

/* Line 1806 of yacc.c  */
#line 772 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 100:

/* Line 1806 of yacc.c  */
#line 774 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 101:

/* Line 1806 of yacc.c  */
#line 776 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 102:

/* Line 1806 of yacc.c  */
#line 778 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 103:

/* Line 1806 of yacc.c  */
#line 780 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 104:

/* Line 1806 of yacc.c  */
#line 782 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 105:

/* Line 1806 of yacc.c  */
#line 784 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 106:

/* Line 1806 of yacc.c  */
#line 786 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 107:

/* Line 1806 of yacc.c  */
#line 788 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 108:

/* Line 1806 of yacc.c  */
#line 790 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 109:

/* Line 1806 of yacc.c  */
#line 792 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 110:

/* Line 1806 of yacc.c  */
#line 794 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 111:

/* Line 1806 of yacc.c  */
#line 796 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 112:

/* Line 1806 of yacc.c  */
#line 798 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 113:

/* Line 1806 of yacc.c  */
#line 800 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 114:

/* Line 1806 of yacc.c  */
#line 802 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 115:

/* Line 1806 of yacc.c  */
#line 804 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 116:

/* Line 1806 of yacc.c  */
#line 806 "smt2newparser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 117:

/* Line 1806 of yacc.c  */
#line 810 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 118:

/* Line 1806 of yacc.c  */
#line 812 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 119:

/* Line 1806 of yacc.c  */
#line 814 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 120:

/* Line 1806 of yacc.c  */
#line 816 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 121:

/* Line 1806 of yacc.c  */
#line 818 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 122:

/* Line 1806 of yacc.c  */
#line 820 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 123:

/* Line 1806 of yacc.c  */
#line 822 "smt2newparser.yy"
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[(1) - (1)].str)); }
    break;

  case 124:

/* Line 1806 of yacc.c  */
#line 824 "smt2newparser.yy"
    {
            (yyval.snode) = new ASTNode(INFO_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(GATTR_T, (yyvsp[(1) - (1)].str)));
        }
    break;



/* Line 1806 of yacc.c  */
#line 2925 "smt2newparser.cc"
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
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
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (&yylloc, context, YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (&yylloc, context, yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }

  yyerror_range[1] = yylloc;

  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
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

  /* Else will try to reuse lookahead token after shifting the error
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

  yyerror_range[1] = yylsp[1-yylen];
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
      if (!yypact_value_is_default (yyn))
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

      yyerror_range[1] = *yylsp;
      yydestruct ("Error: popping",
		  yystos[yystate], yyvsp, yylsp, context);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  *++yyvsp = yylval;

  yyerror_range[2] = yylloc;
  /* Using YYLLOC is tempting, but would change the location of
     the lookahead.  YYLOC is available though.  */
  YYLLOC_DEFAULT (yyloc, yyerror_range, 2);
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

#if !defined(yyoverflow) || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (&yylloc, context, YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval, &yylloc, context);
    }
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



/* Line 2067 of yacc.c  */
#line 831 "smt2newparser.yy"


//=======================================================================================
// Auxiliary Routines


