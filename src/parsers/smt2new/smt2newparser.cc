/* A Bison parser, made by GNU Bison 3.0.2.  */

/* Bison implementation for Yacc-like parsers in C

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
#define YYBISON_VERSION "3.0.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 1

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1


/* Substitute the variable and function names.  */
#define yyparse         smt2newparse
#define yylex           smt2newlex
#define yyerror         smt2newerror
#define yydebug         smt2newdebug
#define yynerrs         smt2newnerrs


/* Copy the first part of user declarations.  */
#line 35 "smt2newparser.yy" /* yacc.c:339  */

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <vector>
#include <list>
#include <string>
#include <string.h>

#include "smt2newcontext.h"
#include "smt2newparser.hh"
#include "smt2tokens.h"

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

#line 102 "smt2newparser.cc" /* yacc.c:339  */

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 1
#endif

/* In a future release of Bison, this section will be replaced
   by #include "y.tab.h".  */
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
#line 66 "smt2newparser.yy" /* yacc.c:355  */

  char  *                      str;
  std::vector< std::string > * str_list;
  ASTNode *                    snode;
  std::list< ASTNode * > *     snode_list;
  smt2token                    tok;

#line 292 "smt2newparser.cc" /* yacc.c:355  */
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

/* Copy the second part of user declarations.  */

#line 320 "smt2newparser.cc" /* yacc.c:358  */

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
#else
typedef signed char yytype_int8;
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
# elif ! defined YYSIZE_T
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
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
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
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
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
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
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
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYSIZE_T yynewbytes;                                            \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / sizeof (*yyptr);                          \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, (Count) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYSIZE_T yyi;                         \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  3
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   374

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  76
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  27
/* YYNRULES -- Number of rules.  */
#define YYNRULES  128
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  243

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   326

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    75,     2,     2,     2,     2,     2,     2,
      72,    73,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,    74,     2,     2,     2,     2,
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
      65,    66,    67,    68,    69,    70,    71
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,    97,    97,   101,   102,   106,   112,   118,   124,   131,
     144,   156,   168,   181,   187,   193,   199,   203,   207,   211,
     215,   221,   227,   231,   237,   241,   247,   253,   259,   263,
     268,   269,   273,   275,   277,   279,   283,   285,   289,   296,
     298,   302,   304,   312,   315,   318,   324,   328,   332,   340,
     343,   351,   353,   355,   357,   359,   363,   365,   369,   371,
     375,   377,   387,   388,   392,   397,   398,   402,   406,   407,
     411,   413,   415,   422,   432,   442,   452,   529,   530,   687,
     700,   706,   712,   718,   724,   730,   736,   742,   748,   754,
     760,   766,   774,   776,   778,   780,   782,   784,   786,   788,
     790,   792,   794,   796,   798,   800,   802,   804,   806,   808,
     810,   812,   814,   816,   818,   820,   822,   824,   826,   828,
     830,   834,   836,   838,   840,   842,   844,   846,   848
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "TK_AS", "TK_DECIMAL", "TK_EXISTS",
  "TK_FORALL", "TK_LET", "TK_NUMERAL", "TK_PAR", "TK_STRING", "TK_ASSERT",
  "TK_CHECKSAT", "TK_DECLARESORT", "TK_DECLAREFUN", "TK_DECLARECONST",
  "TK_DEFINESORT", "TK_DEFINEFUN", "TK_EXIT", "TK_GETASSERTIONS",
  "TK_GETASSIGNMENT", "TK_GETINFO", "TK_GETOPTION", "TK_GETPROOF",
  "TK_GETUNSATCORE", "TK_GETVALUE", "TK_POP", "TK_PUSH", "TK_SETLOGIC",
  "TK_SETINFO", "TK_SETOPTION", "TK_THEORY", "TK_GETITPS", "TK_WRSTATE",
  "TK_RDSTATE", "TK_SIMPLIFY", "TK_NUM", "TK_SYM", "TK_KEY", "TK_STR",
  "TK_DEC", "TK_HEX", "TK_BIN", "KW_SORTS", "KW_FUNS",
  "KW_SORTSDESCRIPTION", "KW_FUNSDESCRIPTION", "KW_DEFINITION", "KW_NOTES",
  "KW_THEORIES", "KW_LANGUAGE", "KW_EXTENSIONS", "KW_VALUES",
  "KW_PRINTSUCCESS", "KW_EXPANDDEFINITIONS", "KW_INTERACTIVEMODE",
  "KW_PRODUCEPROOFS", "KW_PRODUCEUNSATCORES", "KW_PRODUCEMODELS",
  "KW_PRODUCEASSIGNMENTS", "KW_REGULAROUTPUTCHANNEL",
  "KW_DIAGNOSTICOUTPUTCHANNEL", "KW_RANDOMSEED", "KW_VERBOSITY",
  "KW_ERRORBEHAVIOR", "KW_NAME", "KW_NAMED", "KW_AUTHORS", "KW_VERSION",
  "KW_STATUS", "KW_REASONUNKNOWN", "KW_ALLSTATISTICS", "'('", "')'", "'_'",
  "'!'", "$accept", "script", "command_list", "command", "attribute_list",
  "attribute", "attribute_value", "identifier", "sort", "sort_list",
  "s_expr", "s_expr_list", "spec_const", "const_val", "numeral_list",
  "qual_identifier", "var_binding_list", "var_binding", "sorted_var_list",
  "sorted_var", "term_list", "term", "symbol_list", "b_value", "option",
  "predef_key", "info_flag", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311,   312,   313,   314,
     315,   316,   317,   318,   319,   320,   321,   322,   323,   324,
     325,   326,    40,    41,    95,    33
};
# endif

#define YYPACT_NINF -159

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-159)))

#define YYTABLE_NINF -1

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
    -159,    11,   -47,  -159,   339,  -159,    73,   -41,    -2,     3,
     110,     8,    17,   -18,     0,     5,    99,   210,    12,    13,
     -12,    48,    51,    58,   244,   278,    31,    72,    77,    44,
    -159,  -159,  -159,  -159,  -159,  -159,     2,  -159,  -159,  -159,
      50,  -159,    92,    68,  -159,  -159,    69,    70,    76,  -159,
    -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,
      71,    80,  -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,
    -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,
    -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,
    -159,    81,  -159,  -159,    73,    82,    83,    86,    85,    87,
      85,   121,   121,   121,   121,   121,   121,   121,   122,   123,
     135,   136,  -159,   100,  -159,   101,   102,  -159,   -24,   104,
     105,   106,     7,   142,    73,    73,  -159,   107,  -159,   108,
    -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,
    -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,
    -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,  -159,
     109,   -16,   112,   112,   113,   146,   244,  -159,  -159,    -1,
     -16,   -11,   -50,    57,   -22,   -13,  -159,   114,   149,  -159,
    -159,   152,  -159,  -159,   -32,  -159,    66,   -16,  -159,   117,
    -159,   -16,   -16,  -159,   118,  -159,  -159,  -159,  -159,  -159,
    -159,  -159,   -16,  -159,   -16,   -45,   -42,    73,   -35,  -159,
    -159,   176,  -159,   119,  -159,   120,    73,  -159,    28,  -159,
     124,    73,    73,   125,    73,  -159,  -159,  -159,  -159,  -159,
     126,  -159,    10,  -159,   127,   129,  -159,   130,  -159,  -159,
    -159,  -159,  -159
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       3,     0,     2,     1,     0,     4,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      51,    39,    55,    52,    53,    54,     0,    60,    70,    71,
       0,    16,     0,     0,    56,    57,     0,     0,     0,    29,
      17,    24,   128,   121,   122,   123,   124,   125,   126,   127,
       0,     0,    92,    93,    94,    95,    96,    98,    99,   100,
     101,    97,   102,   103,   104,   105,   106,   107,   108,   109,
     110,   111,   112,   113,   114,   115,   116,   117,   118,   119,
     120,     0,    18,    22,     0,     0,     0,     0,    32,     0,
      34,   102,   103,   104,   105,   106,   107,   108,   109,   110,
     111,   112,    91,     0,    19,     0,     0,    28,     0,     0,
       0,     0,     0,     0,     0,     0,    15,     0,    44,     0,
      77,    65,    27,    25,    26,    68,    14,    13,     5,    37,
      49,    33,    36,     7,    35,    79,    80,    81,    82,    83,
      84,    85,    86,    87,    88,    89,    90,     6,    20,    21,
       0,     0,     0,     0,     0,     0,     0,    68,     8,     0,
       0,     0,     0,     0,     0,     0,    41,     0,     0,    65,
      65,     0,    62,    59,     0,    30,     0,     0,    43,     0,
      78,     0,     0,    66,     0,    69,    46,    47,    49,    38,
      50,    45,     0,    61,     0,     0,     0,     0,     0,    58,
      40,     0,    72,     0,    11,     0,     0,    23,     0,    44,
       0,     0,     0,     0,     0,    63,    76,    31,    10,     9,
       0,    48,     0,    67,     0,     0,    64,     0,    12,    42,
      75,    74,    73
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -159,  -159,  -159,  -159,  -159,   -23,    94,  -112,  -158,   -15,
    -159,    -3,    -9,  -159,  -159,   160,  -159,     4,  -137,  -110,
      38,    -6,  -159,    29,  -159,   189,  -159
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     1,     2,     5,   211,    99,   141,    37,   188,   169,
     200,   174,    38,    46,   184,    39,   208,   182,   172,   193,
     173,   195,   171,   146,   113,   100,    60
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint8 yytable[] =
{
      40,    45,   112,   177,   209,   118,   161,   119,   120,   121,
     118,     3,   189,    31,    30,   196,   197,    32,    33,    34,
      35,    31,   178,   192,    31,     4,   190,   178,   221,   213,
     178,   222,    41,   215,   216,    42,    31,   181,   224,    31,
      43,   210,   205,   206,   219,    47,   220,    31,   160,   176,
     198,   199,   179,   180,    48,    49,   175,   176,   176,   160,
      94,   123,   191,   202,    30,   196,   197,    32,    33,    34,
      35,   175,   187,    50,   122,   176,   123,   124,    51,   176,
     176,   123,   175,   239,    95,    92,    93,    96,   135,   142,
     176,   142,   176,    30,    31,    97,    32,    33,    34,    35,
     198,   231,    30,    31,   114,    32,    33,    34,    35,    30,
      31,   115,    32,    33,    34,    35,   116,   117,   166,   167,
     176,    30,   139,   126,    32,    33,    34,    35,   127,    36,
     194,   147,   148,   149,   150,   151,   152,    52,    36,   212,
     128,   129,   130,   185,   132,    36,    30,    44,   131,    32,
      33,    34,    35,   133,   134,   136,   137,   140,   145,   138,
     143,   153,   154,    53,    54,   201,    55,    56,    57,    58,
      59,   155,   156,   157,   158,   159,   162,   163,   164,   165,
     168,   170,   183,   123,   178,   181,   204,   203,   227,   207,
     214,   217,   228,   229,   144,   218,   125,   233,   236,   238,
     240,   223,   241,   242,   232,   186,    91,     0,     0,   201,
     230,     0,   225,     0,    98,   234,   235,     0,   237,    62,
      63,    64,    65,    66,    67,    68,    69,    70,    71,    72,
      73,    74,    75,    76,    77,    78,    79,    80,    81,    82,
      83,    84,    85,    86,    87,    88,    89,    90,    61,   226,
       0,     0,     0,    62,    63,    64,    65,    66,    67,    68,
      69,    70,    71,    72,    73,    74,    75,    76,    77,    78,
      79,    80,    81,    82,    83,    84,    85,    86,    87,    88,
      89,    90,    98,     0,     0,     0,     0,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    82,    83,    84,
      85,    86,    87,    88,    89,    90,    98,     0,     0,     0,
       0,    62,    63,    64,    65,    66,    67,    68,    69,    70,
      71,   101,   102,   103,   104,   105,   106,   107,   108,   109,
     110,   111,    83,    84,    85,    86,    87,    88,    89,    90,
       6,     7,     8,     9,    10,    11,    12,    13,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
       0,    26,    27,    28,    29
};

static const yytype_int16 yycheck[] =
{
       6,    10,    25,   161,    36,     3,   118,     5,     6,     7,
       3,     0,   170,    37,    36,    37,    38,    39,    40,    41,
      42,    37,    72,    73,    37,    72,    37,    72,    73,   187,
      72,    73,    73,   191,   192,    37,    37,    72,    73,    37,
      37,    73,   179,   180,   202,    37,   204,    37,    72,   161,
      72,    73,   162,   163,    37,    73,    72,   169,   170,    72,
      72,    74,    73,   175,    36,    37,    38,    39,    40,    41,
      42,    72,    73,    73,    72,   187,    74,    75,    73,   191,
     192,    74,    72,    73,    36,    73,    73,    36,    94,    98,
     202,   100,   204,    36,    37,    37,    39,    40,    41,    42,
      72,    73,    36,    37,    73,    39,    40,    41,    42,    36,
      37,    39,    39,    40,    41,    42,    39,    73,   124,   125,
     232,    36,    37,    73,    39,    40,    41,    42,    36,    72,
      73,   102,   103,   104,   105,   106,   107,    38,    72,    73,
      72,    72,    72,   166,    73,    72,    36,    37,    72,    39,
      40,    41,    42,    73,    73,    73,    73,    72,    37,    73,
      73,    39,    39,    64,    65,   174,    67,    68,    69,    70,
      71,    36,    36,    73,    73,    73,    72,    72,    72,    37,
      73,    73,    36,    74,    72,    72,    37,    73,   211,    37,
      73,    73,    73,    73,   100,   198,    36,    73,    73,    73,
      73,   207,    73,    73,   219,   167,    17,    -1,    -1,   218,
     216,    -1,   208,    -1,    38,   221,   222,    -1,   224,    43,
      44,    45,    46,    47,    48,    49,    50,    51,    52,    53,
      54,    55,    56,    57,    58,    59,    60,    61,    62,    63,
      64,    65,    66,    67,    68,    69,    70,    71,    38,    73,
      -1,    -1,    -1,    43,    44,    45,    46,    47,    48,    49,
      50,    51,    52,    53,    54,    55,    56,    57,    58,    59,
      60,    61,    62,    63,    64,    65,    66,    67,    68,    69,
      70,    71,    38,    -1,    -1,    -1,    -1,    43,    44,    45,
      46,    47,    48,    49,    50,    51,    52,    53,    54,    55,
      56,    57,    58,    59,    60,    61,    62,    63,    64,    65,
      66,    67,    68,    69,    70,    71,    38,    -1,    -1,    -1,
      -1,    43,    44,    45,    46,    47,    48,    49,    50,    51,
      52,    53,    54,    55,    56,    57,    58,    59,    60,    61,
      62,    63,    64,    65,    66,    67,    68,    69,    70,    71,
      11,    12,    13,    14,    15,    16,    17,    18,    19,    20,
      21,    22,    23,    24,    25,    26,    27,    28,    29,    30,
      -1,    32,    33,    34,    35
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    77,    78,     0,    72,    79,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    32,    33,    34,    35,
      36,    37,    39,    40,    41,    42,    72,    83,    88,    91,
      97,    73,    37,    37,    37,    88,    89,    37,    37,    73,
      73,    73,    38,    64,    65,    67,    68,    69,    70,    71,
     102,    38,    43,    44,    45,    46,    47,    48,    49,    50,
      51,    52,    53,    54,    55,    56,    57,    58,    59,    60,
      61,    62,    63,    64,    65,    66,    67,    68,    69,    70,
      71,   101,    73,    73,    72,    36,    36,    37,    38,    81,
     101,    53,    54,    55,    56,    57,    58,    59,    60,    61,
      62,    63,    81,   100,    73,    39,    39,    73,     3,     5,
       6,     7,    72,    74,    75,    91,    73,    36,    72,    72,
      72,    72,    73,    73,    73,    97,    73,    73,    73,    37,
      72,    82,    88,    73,    82,    37,    99,    99,    99,    99,
      99,    99,    99,    39,    39,    36,    36,    73,    73,    73,
      72,    83,    72,    72,    72,    37,    97,    97,    73,    85,
      73,    98,    94,    96,    87,    72,    83,    84,    72,    95,
      95,    72,    93,    36,    90,    81,    96,    73,    84,    84,
      37,    73,    73,    95,    73,    97,    37,    38,    72,    73,
      86,    88,    83,    73,    37,    94,    94,    37,    92,    36,
      73,    80,    73,    84,    73,    84,    84,    73,    87,    84,
      84,    73,    73,    97,    73,    93,    73,    81,    73,    73,
      97,    73,    85,    73,    97,    97,    73,    97,    73,    73,
      73,    73,    73
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    76,    77,    78,    78,    79,    79,    79,    79,    79,
      79,    79,    79,    79,    79,    79,    79,    79,    79,    79,
      79,    79,    79,    79,    79,    79,    79,    79,    79,    79,
      80,    80,    81,    81,    81,    81,    82,    82,    82,    83,
      83,    84,    84,    85,    85,    86,    86,    86,    86,    87,
      87,    88,    88,    88,    88,    88,    89,    89,    90,    90,
      91,    91,    92,    92,    93,    94,    94,    95,    96,    96,
      97,    97,    97,    97,    97,    97,    97,    98,    98,    99,
     100,   100,   100,   100,   100,   100,   100,   100,   100,   100,
     100,   100,   101,   101,   101,   101,   101,   101,   101,   101,
     101,   101,   101,   101,   101,   101,   101,   101,   101,   101,
     101,   101,   101,   101,   101,   101,   101,   101,   101,   101,
     101,   102,   102,   102,   102,   102,   102,   102,   102
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     0,     2,     4,     4,     4,     5,     8,
       8,     7,     9,     4,     4,     4,     3,     3,     3,     3,
       4,     4,     3,     7,     3,     4,     4,     4,     3,     3,
       0,     2,     1,     2,     1,     2,     1,     1,     3,     1,
       5,     1,     5,     2,     0,     1,     1,     1,     3,     0,
       2,     1,     1,     1,     1,     1,     1,     1,     2,     1,
       1,     5,     0,     2,     4,     0,     2,     4,     0,     2,
       1,     1,     5,     8,     8,     8,     6,     0,     2,     1,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                  \
do                                                              \
  if (yychar == YYEMPTY)                                        \
    {                                                           \
      yychar = (Token);                                         \
      yylval = (Value);                                         \
      YYPOPSTACK (yylen);                                       \
      yystate = *yyssp;                                         \
      goto yybackup;                                            \
    }                                                           \
  else                                                          \
    {                                                           \
      yyerror (&yylloc, context, YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)                                \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;        \
          (Current).first_column = YYRHSLOC (Rhs, 1).first_column;      \
          (Current).last_line    = YYRHSLOC (Rhs, N).last_line;         \
          (Current).last_column  = YYRHSLOC (Rhs, N).last_column;       \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).first_line   = (Current).last_line   =              \
            YYRHSLOC (Rhs, 0).last_line;                                \
          (Current).first_column = (Current).last_column =              \
            YYRHSLOC (Rhs, 0).last_column;                              \
        }                                                               \
    while (0)
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K])


/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL

/* Print *YYLOCP on YYO.  Private, do not rely on its existence. */

YY_ATTRIBUTE_UNUSED
static unsigned
yy_location_print_ (FILE *yyo, YYLTYPE const * const yylocp)
{
  unsigned res = 0;
  int end_col = 0 != yylocp->last_column ? yylocp->last_column - 1 : 0;
  if (0 <= yylocp->first_line)
    {
      res += YYFPRINTF (yyo, "%d", yylocp->first_line);
      if (0 <= yylocp->first_column)
        res += YYFPRINTF (yyo, ".%d", yylocp->first_column);
    }
  if (0 <= yylocp->last_line)
    {
      if (yylocp->first_line < yylocp->last_line)
        {
          res += YYFPRINTF (yyo, "-%d", yylocp->last_line);
          if (0 <= end_col)
            res += YYFPRINTF (yyo, ".%d", end_col);
        }
      else if (0 <= end_col && yylocp->first_column < end_col)
        res += YYFPRINTF (yyo, "-%d", end_col);
    }
  return res;
 }

#  define YY_LOCATION_PRINT(File, Loc)          \
  yy_location_print_ (File, &(Loc))

# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value, Location, context); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, Smt2newContext* context)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  YYUSE (yylocationp);
  YYUSE (context);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# endif
  YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp, Smt2newContext* context)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  YY_LOCATION_PRINT (yyoutput, *yylocationp);
  YYFPRINTF (yyoutput, ": ");
  yy_symbol_value_print (yyoutput, yytype, yyvaluep, yylocationp, context);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, YYLTYPE *yylsp, int yyrule, Smt2newContext* context)
{
  unsigned long int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[yyssp[yyi + 1 - yynrhs]],
                       &(yyvsp[(yyi + 1) - (yynrhs)])
                       , &(yylsp[(yyi + 1) - (yynrhs)])                       , context);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, yylsp, Rule, context); \
} while (0)

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
#ifndef YYINITDEPTH
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
static YYSIZE_T
yystrlen (const char *yystr)
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
static char *
yystpcpy (char *yydest, const char *yysrc)
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
  YYSIZE_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
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
                {
                  YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (! (yysize <= yysize1
                         && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                    return 2;
                  yysize = yysize1;
                }
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

  {
    YYSIZE_T yysize1 = yysize + yystrlen (yyformat);
    if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
      return 2;
    yysize = yysize1;
  }

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

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, YYLTYPE *yylocationp, Smt2newContext* context)
{
  YYUSE (yyvaluep);
  YYUSE (yylocationp);
  YYUSE (context);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/*----------.
| yyparse.  |
`----------*/

int
yyparse (Smt2newContext* context)
{
/* The lookahead symbol.  */
int yychar;


/* The semantic value of the lookahead symbol.  */
/* Default value used for initialization, for pacifying older GCCs
   or non-GCC compilers.  */
YY_INITIAL_VALUE (static YYSTYPE yyval_default;)
YYSTYPE yylval YY_INITIAL_VALUE (= yyval_default);

/* Location data for the lookahead symbol.  */
static YYLTYPE yyloc_default
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL
  = { 1, 1, 1, 1 }
# endif
;
YYLTYPE yylloc = yyloc_default;

    /* Number of syntax errors so far.  */
    int yynerrs;

    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.
       'yyls': related to locations.

       Refer to the stacks through separate pointers, to allow yyoverflow
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
  int yytoken = 0;
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

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yylsp = yyls = yylsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  yylsp[0] = yylloc;
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
      yychar = yylex (&yylval, &yylloc, scanner);
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
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END
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
     '$$ = $1'.

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
#line 97 "smt2newparser.yy" /* yacc.c:1646  */
    { ASTNode *n = new ASTNode(CMDL_T, strdup("main-script")); n->children = (yyvsp[0].snode_list); context->insertRoot(n); }
#line 1709 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 3:
#line 101 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
#line 1715 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 4:
#line 103 "smt2newparser.yy" /* yacc.c:1646  */
    { (*(yyvsp[-1].snode_list)).push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 1721 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 5:
#line 107 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[-1].str)));
        }
#line 1731 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 6:
#line 113 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 1741 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 7:
#line 119 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 1751 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 8:
#line 125 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-3].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[-2].str)));
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[-1].str)));
        }
#line 1762 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 9:
#line 132 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-6].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[-5].str)));

            ASTNode* syml = new ASTNode(SYML_T, NULL);
            syml->children = (yyvsp[-3].snode_list);
            (yyval.snode)->children->push_back(syml);

            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 1778 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 10:
#line 145 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-6].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[-5].str)));

            ASTNode* sortl = new ASTNode(SORTL_T, NULL);
            sortl->children = (yyvsp[-3].snode_list);
            (yyval.snode)->children->push_back(sortl);

            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 1794 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 11:
#line 157 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-5].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-4].snode));

            ASTNode* sortl = new ASTNode(SORTL_T, NULL);
            sortl->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(sortl);

            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 1810 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 12:
#line 169 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-7].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[-6].str)));

            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = (yyvsp[-4].snode_list);
            (yyval.snode)->children->push_back(svl);

            (yyval.snode)->children->push_back((yyvsp[-2].snode));
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 1827 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 13:
#line 182 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[-1].str)));
        }
#line 1837 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 14:
#line 188 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[-1].str)));
        }
#line 1847 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 15:
#line 194 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 1857 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 16:
#line 200 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 1865 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 17:
#line 204 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 1873 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 18:
#line 208 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 1881 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 19:
#line 212 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 1889 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 20:
#line 216 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[-1].str)));
        }
#line 1899 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 21:
#line 222 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[-1].str)));
        }
#line 1909 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 22:
#line 228 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 1917 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 23:
#line 232 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-5].tok));
            (yyval.snode)->children = (yyvsp[-2].snode_list);
            (yyval.snode)->children->push_front((yyvsp[-3].snode));
        }
#line 1927 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 24:
#line 238 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 1935 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 25:
#line 242 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[-1].str)));
        }
#line 1945 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 26:
#line 248 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(PATTR_T, (yyvsp[-1].str)));
        }
#line 1955 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 27:
#line 254 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 1965 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 28:
#line 260 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 1973 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 29:
#line 264 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok)); }
#line 1979 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 30:
#line 268 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
#line 1985 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 31:
#line 270 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 1991 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 32:
#line 274 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(UATTR_T, (yyvsp[0].str)); }
#line 1997 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 33:
#line 276 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(UATTR_T, (yyvsp[-1].str)); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 2003 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 34:
#line 278 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(PATTR_T, (yyvsp[0].str)); }
#line 2009 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 35:
#line 280 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(PATTR_T, (yyvsp[-1].str)); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 2015 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 36:
#line 284 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(SPECC_T, NULL); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 2021 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 37:
#line 286 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(SYM_T, (yyvsp[0].str));
        }
#line 2029 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 38:
#line 290 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(SEXPRL_T, NULL);
            (yyval.snode)->children = (yyvsp[-1].snode_list);
        }
#line 2038 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 39:
#line 297 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(SYM_T, (yyvsp[0].str)); }
#line 2044 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 40:
#line 299 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(SYM_T, (yyvsp[-2].str)); (yyval.snode)->children = (yyvsp[-1].snode_list); }
#line 2050 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 41:
#line 303 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(ID_T, NULL); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 2056 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 42:
#line 305 "smt2newparser.yy" /* yacc.c:1646  */
    {
        (yyval.snode) = new ASTNode(LID_T, NULL);
        (yyval.snode)->children = (yyvsp[-1].snode_list);
        (yyval.snode)->children->push_front((yyvsp[-2].snode));
      }
#line 2066 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 43:
#line 313 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2072 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 44:
#line 315 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
#line 2078 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 45:
#line 319 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(SPECC_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2088 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 46:
#line 325 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(SYM_T, (yyvsp[0].str));
        }
#line 2096 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 47:
#line 329 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(UATTR_T, (yyvsp[0].str));
        }
#line 2104 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 48:
#line 333 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(SEXPRL_T, NULL);
            (yyval.snode)->children = (yyvsp[-1].snode_list);
        }
#line 2113 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 49:
#line 340 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode_list) = new std::list<ASTNode*>();
        }
#line 2121 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 50:
#line 344 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode));
            (yyval.snode_list) = (yyvsp[-1].snode_list);
        }
#line 2130 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 51:
#line 352 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(NUM_T, (yyvsp[0].str)); }
#line 2136 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 52:
#line 354 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(DEC_T, (yyvsp[0].str)); }
#line 2142 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 53:
#line 356 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(HEX_T, (yyvsp[0].str)); }
#line 2148 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 54:
#line 358 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(BIN_T, (yyvsp[0].str)); }
#line 2154 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 55:
#line 360 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(STR_T, (yyvsp[0].str)); }
#line 2160 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 56:
#line 364 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(SYM_T, (yyvsp[0].str)); }
#line 2166 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 57:
#line 366 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = (yyvsp[0].snode); }
#line 2172 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 58:
#line 370 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyvsp[-1].snode_list)->push_back(new ASTNode(NUM_T, (yyvsp[0].str))); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2178 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 59:
#line 372 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); (yyval.snode_list)->push_back(new ASTNode(NUM_T, (yyvsp[0].str))); }
#line 2184 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 60:
#line 376 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = (yyvsp[0].snode); }
#line 2190 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 61:
#line 378 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(AS_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-2].snode));
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2201 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 62:
#line 387 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
#line 2207 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 63:
#line 389 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2213 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 64:
#line 393 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(VARB_T, (yyvsp[-2].str)); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[-1].snode)); }
#line 2219 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 65:
#line 397 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
#line 2225 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 66:
#line 399 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2231 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 67:
#line 403 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(SV_T, (yyvsp[-2].str));  (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[-1].snode)); }
#line 2237 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 68:
#line 406 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
#line 2243 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 69:
#line 408 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2249 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 70:
#line 412 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(TERM_T, NULL); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 2255 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 71:
#line 414 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(QID_T, NULL); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 2261 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 72:
#line 416 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(LQID_T, NULL);
            (yyval.snode)->children = (yyvsp[-1].snode_list);
            (yyval.snode)->children->push_front((yyvsp[-2].snode));
            (yyval.snode)->children->push_front((yyvsp[-3].snode));
        }
#line 2272 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 73:
#line 423 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(LET_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyvsp[-3].snode_list)->push_front((yyvsp[-4].snode));
            ASTNode* vbl = new ASTNode(VARBL_T, NULL);
            vbl->children = (yyvsp[-3].snode_list);
            (yyval.snode)->children->push_back(vbl);
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2286 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 74:
#line 433 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(FORALL_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyvsp[-3].snode_list)->push_front((yyvsp[-4].snode));
            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = (yyvsp[-3].snode_list);
            (yyval.snode)->children->push_back(svl);
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2300 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 75:
#line 443 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(EXISTS_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyvsp[-3].snode_list)->push_front((yyvsp[-4].snode));
            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = (yyvsp[-3].snode_list);
            (yyval.snode)->children->push_back(svl);
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2314 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 76:
#line 453 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(BANG_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_front((yyvsp[-3].snode));
            ASTNode *atrs = new ASTNode(GATTRL_T, NULL);
            (yyvsp[-1].snode_list)->push_front((yyvsp[-2].snode));
            atrs->children = (yyvsp[-1].snode_list);
            (yyval.snode)->children->push_back(atrs);
        }
#line 2328 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 77:
#line 529 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
#line 2334 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 78:
#line 531 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyvsp[-1].snode_list)->push_back(new ASTNode(SYM_T, (yyvsp[0].str))); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2340 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 79:
#line 688 "smt2newparser.yy" /* yacc.c:1646  */
    {
            if (strcmp((yyvsp[0].str), "true") == 0)
                (yyval.snode) = new ASTNode(BOOL_T, strdup("true"));
            else if (strcmp((yyvsp[0].str), "false") == 0)
                (yyval.snode) = new ASTNode(BOOL_T, strdup("false"));
            else {
                printf("Syntax error: expecting either 'true' or 'false', got '%s'\n", (yyvsp[0].str));
                YYERROR;
            }
        }
#line 2355 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 80:
#line 701 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2365 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 81:
#line 707 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2375 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 82:
#line 713 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2385 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 83:
#line 719 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2395 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 84:
#line 725 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2405 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 85:
#line 731 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2415 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 86:
#line 737 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2425 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 87:
#line 743 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(STR_T, (yyvsp[0].str)));
        }
#line 2435 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 88:
#line 749 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(STR_T, (yyvsp[0].str)));
        }
#line 2445 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 89:
#line 755 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[0].str)));
        }
#line 2455 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 90:
#line 761 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[0].str)));
        }
#line 2465 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 91:
#line 767 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2475 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 92:
#line 775 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2481 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 93:
#line 777 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2487 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 94:
#line 779 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2493 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 95:
#line 781 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2499 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 96:
#line 783 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2505 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 97:
#line 785 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2511 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 98:
#line 787 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2517 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 99:
#line 789 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2523 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 100:
#line 791 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2529 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 101:
#line 793 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2535 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 102:
#line 795 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2541 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 103:
#line 797 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2547 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 104:
#line 799 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2553 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 105:
#line 801 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2559 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 106:
#line 803 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2565 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 107:
#line 805 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2571 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 108:
#line 807 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2577 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 109:
#line 809 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2583 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 110:
#line 811 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2589 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 111:
#line 813 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2595 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 112:
#line 815 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2601 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 113:
#line 817 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2607 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 114:
#line 819 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2613 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 115:
#line 821 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2619 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 116:
#line 823 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2625 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 117:
#line 825 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2631 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 118:
#line 827 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2637 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 119:
#line 829 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2643 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 120:
#line 831 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2649 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 121:
#line 835 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 2655 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 122:
#line 837 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 2661 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 123:
#line 839 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 2667 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 124:
#line 841 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 2673 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 125:
#line 843 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 2679 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 126:
#line 845 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 2685 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 127:
#line 847 "smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 2691 "smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 128:
#line 849 "smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(INFO_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(GATTR_T, (yyvsp[0].str)));
        }
#line 2701 "smt2newparser.cc" /* yacc.c:1646  */
    break;


#line 2705 "smt2newparser.cc" /* yacc.c:1646  */
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

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
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
  /* Do not reclaim the symbols of the rule whose action triggered
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
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

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

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

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

#if !defined yyoverflow || YYERROR_VERBOSE
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
  /* Do not reclaim the symbols of the rule whose action triggered
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
  return yyresult;
}
#line 856 "smt2newparser.yy" /* yacc.c:1906  */


//=======================================================================================
// Auxiliary Routines

