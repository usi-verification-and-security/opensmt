/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison implementation for Yacc-like parsers in C

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
#define YYBISON_VERSION "3.0.4"

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
#line 35 "smt2new/smt2newparser.yy" /* yacc.c:339  */

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

#line 102 "smt2new/smt2newparser.cc" /* yacc.c:339  */

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
   by #include "smt2newparser.hh".  */
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
#line 66 "smt2new/smt2newparser.yy" /* yacc.c:355  */

  char  *                      str;
  std::vector< std::string > * str_list;
  ASTNode *                    snode;
  std::list< ASTNode * > *     snode_list;
  smt2token                    tok;

#line 223 "smt2new/smt2newparser.cc" /* yacc.c:355  */
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

/* Copy the second part of user declarations.  */

#line 253 "smt2new/smt2newparser.cc" /* yacc.c:358  */

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
#define YYLAST   378

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  77
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  27
/* YYNRULES -- Number of rules.  */
#define YYNRULES  129
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  246

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   327

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    76,     2,     2,     2,     2,     2,     2,
      73,    74,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,    75,     2,     2,     2,     2,
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
      65,    66,    67,    68,    69,    70,    71,    72
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,    97,    97,   101,   102,   106,   112,   118,   124,   131,
     144,   156,   168,   181,   187,   193,   199,   203,   207,   211,
     215,   221,   227,   233,   237,   243,   247,   253,   259,   265,
     269,   274,   275,   279,   281,   283,   285,   289,   291,   295,
     302,   304,   308,   310,   318,   321,   324,   330,   334,   338,
     346,   349,   357,   359,   361,   363,   365,   369,   371,   375,
     377,   381,   383,   393,   394,   398,   403,   404,   408,   412,
     413,   417,   419,   421,   428,   438,   448,   458,   535,   536,
     693,   706,   712,   718,   724,   730,   736,   742,   748,   754,
     760,   766,   772,   780,   782,   784,   786,   788,   790,   792,
     794,   796,   798,   800,   802,   804,   806,   808,   810,   812,
     814,   816,   818,   820,   822,   824,   826,   828,   830,   832,
     834,   836,   840,   842,   844,   846,   848,   850,   852,   854
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
  "TK_RDSTATE", "TK_SIMPLIFY", "TK_WRFUNS", "TK_NUM", "TK_SYM", "TK_KEY",
  "TK_STR", "TK_DEC", "TK_HEX", "TK_BIN", "KW_SORTS", "KW_FUNS",
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
     325,   326,   327,    40,    41,    95,    33
};
# endif

#define YYPACT_NINF -161

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-161)))

#define YYTABLE_NINF -1

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
    -161,    10,   -58,  -161,   342,  -161,    -1,   -10,    27,    29,
     112,    32,    33,     3,     5,    11,   104,   212,    12,    13,
       1,    43,    47,    50,   246,   280,    17,    54,    65,    36,
      73,  -161,  -161,  -161,  -161,  -161,  -161,     0,  -161,  -161,
    -161,    44,  -161,    82,    49,  -161,  -161,    53,    61,    62,
    -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,
    -161,    57,    63,  -161,  -161,  -161,  -161,  -161,  -161,  -161,
    -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,
    -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,
    -161,  -161,    64,  -161,  -161,    -1,    67,    68,    70,    87,
      71,    87,    98,    98,    98,    98,    98,    98,    98,   111,
     116,   120,   121,  -161,    85,  -161,    93,    97,  -161,   103,
     -22,   105,   106,   107,     6,   143,    -1,    -1,  -161,   108,
    -161,   109,  -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,
    -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,
    -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,  -161,
    -161,  -161,  -161,   110,   -14,   113,   113,   114,   147,   246,
    -161,  -161,   -11,   -14,   -24,   -48,    66,   -20,   -27,  -161,
     115,   150,  -161,  -161,   152,  -161,  -161,   -25,  -161,    74,
     -14,  -161,   118,  -161,   -14,   -14,  -161,   119,  -161,  -161,
    -161,  -161,  -161,  -161,  -161,   -14,  -161,   -14,   -45,   -42,
      -1,   -30,  -161,  -161,   178,  -161,   122,  -161,   123,    -1,
    -161,    59,  -161,   124,    -1,    -1,   125,    -1,  -161,  -161,
    -161,  -161,  -161,   126,  -161,    -5,  -161,   127,   128,  -161,
     129,  -161,  -161,  -161,  -161,  -161
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       3,     0,     2,     1,     0,     4,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    52,    40,    56,    53,    54,    55,     0,    61,    71,
      72,     0,    16,     0,     0,    57,    58,     0,     0,     0,
      30,    17,    25,   129,   122,   123,   124,   125,   126,   127,
     128,     0,     0,    93,    94,    95,    96,    97,    99,   100,
     101,   102,    98,   103,   104,   105,   106,   107,   108,   109,
     110,   111,   112,   113,   114,   115,   116,   117,   118,   119,
     120,   121,     0,    18,    23,     0,     0,     0,     0,    33,
       0,    35,   103,   104,   105,   106,   107,   108,   109,   110,
     111,   112,   113,    92,     0,    19,     0,     0,    29,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    15,     0,
      45,     0,    78,    66,    28,    26,    27,    69,    14,    13,
       5,    38,    50,    34,    37,     7,    36,    80,    81,    82,
      83,    84,    85,    86,    87,    88,    89,    90,    91,     6,
      20,    21,    22,     0,     0,     0,     0,     0,     0,     0,
      69,     8,     0,     0,     0,     0,     0,     0,     0,    42,
       0,     0,    66,    66,     0,    63,    60,     0,    31,     0,
       0,    44,     0,    79,     0,     0,    67,     0,    70,    47,
      48,    50,    39,    51,    46,     0,    62,     0,     0,     0,
       0,     0,    59,    41,     0,    73,     0,    11,     0,     0,
      24,     0,    45,     0,     0,     0,     0,     0,    64,    77,
      32,    10,     9,     0,    49,     0,    68,     0,     0,    65,
       0,    12,    43,    76,    75,    74
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -161,  -161,  -161,  -161,  -161,   -23,    94,  -112,  -160,   -28,
    -161,     4,    -9,  -161,  -161,   169,  -161,    -4,  -127,  -108,
      38,    -6,  -161,    58,  -161,   192,  -161
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     1,     2,     5,   214,   100,   143,    38,   191,   172,
     203,   177,    39,    47,   187,    40,   211,   185,   175,   196,
     176,   198,   174,   148,   114,   101,    61
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint8 yytable[] =
{
      41,    46,   113,   120,   180,   121,   122,   123,   164,   120,
       3,    32,   212,   192,   193,     4,    32,    31,   199,   200,
      33,    34,    35,    36,    32,   181,   195,    32,   181,   224,
     216,   181,   225,    32,   218,   219,    31,    32,    32,    33,
      34,    35,    36,   184,   227,   222,   163,   223,   125,   213,
     194,   163,   179,   201,   202,   208,   209,   182,   183,   178,
     179,   179,   178,   190,    42,    43,   205,    44,   178,   242,
      48,    49,    37,   124,    95,   125,   126,    50,   179,    51,
      96,   125,   179,   179,    97,    52,    93,    94,    98,   137,
     144,   115,   144,   179,   116,   179,    31,   199,   200,    33,
      34,    35,    36,    31,    32,   117,    33,    34,    35,    36,
     118,    31,    32,   119,    33,    34,    35,    36,   128,   129,
     169,   170,   130,   179,    31,   141,   131,    33,    34,    35,
      36,   134,   201,   234,   132,   133,   147,   135,   136,    37,
     197,   138,   139,    53,   140,   145,   188,    37,   215,    31,
      45,   155,    33,    34,    35,    36,   156,   157,   158,   159,
     142,   149,   150,   151,   152,   153,   154,   160,   204,    54,
      55,   161,    56,    57,    58,    59,    60,   162,   165,   166,
     167,   168,   171,   173,   186,   125,   181,   184,   207,   206,
     210,   230,   217,   220,   235,   146,   231,   232,   236,   239,
     241,   243,   244,   245,   226,   221,   127,   228,   189,    92,
       0,     0,   204,   233,     0,     0,     0,    99,   237,   238,
       0,   240,    63,    64,    65,    66,    67,    68,    69,    70,
      71,    72,    73,    74,    75,    76,    77,    78,    79,    80,
      81,    82,    83,    84,    85,    86,    87,    88,    89,    90,
      91,    62,   229,     0,     0,     0,    63,    64,    65,    66,
      67,    68,    69,    70,    71,    72,    73,    74,    75,    76,
      77,    78,    79,    80,    81,    82,    83,    84,    85,    86,
      87,    88,    89,    90,    91,    99,     0,     0,     0,     0,
      63,    64,    65,    66,    67,    68,    69,    70,    71,    72,
      73,    74,    75,    76,    77,    78,    79,    80,    81,    82,
      83,    84,    85,    86,    87,    88,    89,    90,    91,    99,
       0,     0,     0,     0,    63,    64,    65,    66,    67,    68,
      69,    70,    71,    72,   102,   103,   104,   105,   106,   107,
     108,   109,   110,   111,   112,    84,    85,    86,    87,    88,
      89,    90,    91,     6,     7,     8,     9,    10,    11,    12,
      13,    14,    15,    16,    17,    18,    19,    20,    21,    22,
      23,    24,    25,     0,    26,    27,    28,    29,    30
};

static const yytype_int16 yycheck[] =
{
       6,    10,    25,     3,   164,     5,     6,     7,   120,     3,
       0,    38,    37,   173,    38,    73,    38,    37,    38,    39,
      40,    41,    42,    43,    38,    73,    74,    38,    73,    74,
     190,    73,    74,    38,   194,   195,    37,    38,    38,    40,
      41,    42,    43,    73,    74,   205,    73,   207,    75,    74,
      74,    73,   164,    73,    74,   182,   183,   165,   166,    73,
     172,   173,    73,    74,    74,    38,   178,    38,    73,    74,
      38,    38,    73,    73,    73,    75,    76,    74,   190,    74,
      37,    75,   194,   195,    37,    74,    74,    74,    38,    95,
      99,    74,   101,   205,    40,   207,    37,    38,    39,    40,
      41,    42,    43,    37,    38,    40,    40,    41,    42,    43,
      74,    37,    38,    40,    40,    41,    42,    43,    74,    37,
     126,   127,    73,   235,    37,    38,    73,    40,    41,    42,
      43,    74,    73,    74,    73,    73,    38,    74,    74,    73,
      74,    74,    74,    39,    74,    74,   169,    73,    74,    37,
      38,    40,    40,    41,    42,    43,    40,    37,    37,    74,
      73,   103,   104,   105,   106,   107,   108,    74,   177,    65,
      66,    74,    68,    69,    70,    71,    72,    74,    73,    73,
      73,    38,    74,    74,    37,    75,    73,    73,    38,    74,
      38,   214,    74,    74,   222,   101,    74,    74,    74,    74,
      74,    74,    74,    74,   210,   201,    37,   211,   170,    17,
      -1,    -1,   221,   219,    -1,    -1,    -1,    39,   224,   225,
      -1,   227,    44,    45,    46,    47,    48,    49,    50,    51,
      52,    53,    54,    55,    56,    57,    58,    59,    60,    61,
      62,    63,    64,    65,    66,    67,    68,    69,    70,    71,
      72,    39,    74,    -1,    -1,    -1,    44,    45,    46,    47,
      48,    49,    50,    51,    52,    53,    54,    55,    56,    57,
      58,    59,    60,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    39,    -1,    -1,    -1,    -1,
      44,    45,    46,    47,    48,    49,    50,    51,    52,    53,
      54,    55,    56,    57,    58,    59,    60,    61,    62,    63,
      64,    65,    66,    67,    68,    69,    70,    71,    72,    39,
      -1,    -1,    -1,    -1,    44,    45,    46,    47,    48,    49,
      50,    51,    52,    53,    54,    55,    56,    57,    58,    59,
      60,    61,    62,    63,    64,    65,    66,    67,    68,    69,
      70,    71,    72,    11,    12,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    25,    26,    27,
      28,    29,    30,    -1,    32,    33,    34,    35,    36
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    78,    79,     0,    73,    80,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    32,    33,    34,    35,
      36,    37,    38,    40,    41,    42,    43,    73,    84,    89,
      92,    98,    74,    38,    38,    38,    89,    90,    38,    38,
      74,    74,    74,    39,    65,    66,    68,    69,    70,    71,
      72,   103,    39,    44,    45,    46,    47,    48,    49,    50,
      51,    52,    53,    54,    55,    56,    57,    58,    59,    60,
      61,    62,    63,    64,    65,    66,    67,    68,    69,    70,
      71,    72,   102,    74,    74,    73,    37,    37,    38,    39,
      82,   102,    54,    55,    56,    57,    58,    59,    60,    61,
      62,    63,    64,    82,   101,    74,    40,    40,    74,    40,
       3,     5,     6,     7,    73,    75,    76,    92,    74,    37,
      73,    73,    73,    73,    74,    74,    74,    98,    74,    74,
      74,    38,    73,    83,    89,    74,    83,    38,   100,   100,
     100,   100,   100,   100,   100,    40,    40,    37,    37,    74,
      74,    74,    74,    73,    84,    73,    73,    73,    38,    98,
      98,    74,    86,    74,    99,    95,    97,    88,    73,    84,
      85,    73,    96,    96,    73,    94,    37,    91,    82,    97,
      74,    85,    85,    38,    74,    74,    96,    74,    98,    38,
      39,    73,    74,    87,    89,    84,    74,    38,    95,    95,
      38,    93,    37,    74,    81,    74,    85,    74,    85,    85,
      74,    88,    85,    85,    74,    74,    98,    74,    94,    74,
      82,    74,    74,    98,    74,    86,    74,    98,    98,    74,
      98,    74,    74,    74,    74,    74
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    77,    78,    79,    79,    80,    80,    80,    80,    80,
      80,    80,    80,    80,    80,    80,    80,    80,    80,    80,
      80,    80,    80,    80,    80,    80,    80,    80,    80,    80,
      80,    81,    81,    82,    82,    82,    82,    83,    83,    83,
      84,    84,    85,    85,    86,    86,    87,    87,    87,    87,
      88,    88,    89,    89,    89,    89,    89,    90,    90,    91,
      91,    92,    92,    93,    93,    94,    95,    95,    96,    97,
      97,    98,    98,    98,    98,    98,    98,    98,    99,    99,
     100,   101,   101,   101,   101,   101,   101,   101,   101,   101,
     101,   101,   101,   102,   102,   102,   102,   102,   102,   102,
     102,   102,   102,   102,   102,   102,   102,   102,   102,   102,
     102,   102,   102,   102,   102,   102,   102,   102,   102,   102,
     102,   102,   103,   103,   103,   103,   103,   103,   103,   103
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     0,     2,     4,     4,     4,     5,     8,
       8,     7,     9,     4,     4,     4,     3,     3,     3,     3,
       4,     4,     4,     3,     7,     3,     4,     4,     4,     3,
       3,     0,     2,     1,     2,     1,     2,     1,     1,     3,
       1,     5,     1,     5,     2,     0,     1,     1,     1,     3,
       0,     2,     1,     1,     1,     1,     1,     1,     1,     2,
       1,     1,     5,     0,     2,     4,     0,     2,     4,     0,
       2,     1,     1,     5,     8,     8,     8,     6,     0,     2,
       1,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1
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
#line 97 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { ASTNode *n = new ASTNode(CMDL_T, strdup("main-script")); n->children = (yyvsp[0].snode_list); context->insertRoot(n); }
#line 1642 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 3:
#line 101 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
#line 1648 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 4:
#line 103 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (*(yyvsp[-1].snode_list)).push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 1654 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 5:
#line 107 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[-1].str)));
        }
#line 1664 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 6:
#line 113 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 1674 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 7:
#line 119 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 1684 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 8:
#line 125 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-3].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[-2].str)));
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[-1].str)));
        }
#line 1695 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 9:
#line 132 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-6].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[-5].str)));

            ASTNode* syml = new ASTNode(SYML_T, NULL);
            syml->children = (yyvsp[-3].snode_list);
            (yyval.snode)->children->push_back(syml);

            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 1711 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 10:
#line 145 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-6].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(SYM_T, (yyvsp[-5].str)));

            ASTNode* sortl = new ASTNode(SORTL_T, NULL);
            sortl->children = (yyvsp[-3].snode_list);
            (yyval.snode)->children->push_back(sortl);

            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 1727 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 11:
#line 157 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-5].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-4].snode));

            ASTNode* sortl = new ASTNode(SORTL_T, NULL);
            sortl->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(sortl);

            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 1743 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 12:
#line 169 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
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
#line 1760 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 13:
#line 182 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[-1].str)));
        }
#line 1770 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 14:
#line 188 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[-1].str)));
        }
#line 1780 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 15:
#line 194 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 1790 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 16:
#line 200 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 1798 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 17:
#line 204 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 1806 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 18:
#line 208 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 1814 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 19:
#line 212 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 1822 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 20:
#line 216 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[-1].str)));
        }
#line 1832 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 21:
#line 222 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[-1].str)));
        }
#line 1842 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 22:
#line 228 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[-1].str)));
        }
#line 1852 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 23:
#line 234 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 1860 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 24:
#line 238 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-5].tok));
            (yyval.snode)->children = (yyvsp[-2].snode_list);
            (yyval.snode)->children->push_front((yyvsp[-3].snode));
        }
#line 1870 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 25:
#line 244 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 1878 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 26:
#line 248 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(UATTR_T, (yyvsp[-1].str)));
        }
#line 1888 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 27:
#line 254 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(PATTR_T, (yyvsp[-1].str)));
        }
#line 1898 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 28:
#line 260 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-2].tok));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 1908 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 29:
#line 266 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok));
        }
#line 1916 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 30:
#line 270 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(CMD_T, (yyvsp[-1].tok)); }
#line 1922 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 31:
#line 274 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
#line 1928 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 32:
#line 276 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 1934 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 33:
#line 280 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(UATTR_T, (yyvsp[0].str)); }
#line 1940 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 34:
#line 282 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(UATTR_T, (yyvsp[-1].str)); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 1946 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 35:
#line 284 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(PATTR_T, (yyvsp[0].str)); }
#line 1952 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 36:
#line 286 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(PATTR_T, (yyvsp[-1].str)); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 1958 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 37:
#line 290 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(SPECC_T, NULL); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 1964 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 38:
#line 292 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(SYM_T, (yyvsp[0].str));
        }
#line 1972 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 39:
#line 296 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(SEXPRL_T, NULL);
            (yyval.snode)->children = (yyvsp[-1].snode_list);
        }
#line 1981 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 40:
#line 303 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(SYM_T, (yyvsp[0].str)); }
#line 1987 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 41:
#line 305 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(SYM_T, (yyvsp[-2].str)); (yyval.snode)->children = (yyvsp[-1].snode_list); }
#line 1993 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 42:
#line 309 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(ID_T, NULL); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 1999 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 43:
#line 311 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
        (yyval.snode) = new ASTNode(LID_T, NULL);
        (yyval.snode)->children = (yyvsp[-1].snode_list);
        (yyval.snode)->children->push_front((yyvsp[-2].snode));
      }
#line 2009 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 44:
#line 319 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2015 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 45:
#line 321 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
#line 2021 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 46:
#line 325 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(SPECC_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2031 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 47:
#line 331 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(SYM_T, (yyvsp[0].str));
        }
#line 2039 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 48:
#line 335 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(UATTR_T, (yyvsp[0].str));
        }
#line 2047 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 49:
#line 339 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(SEXPRL_T, NULL);
            (yyval.snode)->children = (yyvsp[-1].snode_list);
        }
#line 2056 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 50:
#line 346 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode_list) = new std::list<ASTNode*>();
        }
#line 2064 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 51:
#line 350 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode));
            (yyval.snode_list) = (yyvsp[-1].snode_list);
        }
#line 2073 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 52:
#line 358 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(NUM_T, (yyvsp[0].str)); }
#line 2079 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 53:
#line 360 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(DEC_T, (yyvsp[0].str)); }
#line 2085 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 54:
#line 362 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(HEX_T, (yyvsp[0].str)); }
#line 2091 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 55:
#line 364 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(BIN_T, (yyvsp[0].str)); }
#line 2097 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 56:
#line 366 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(STR_T, (yyvsp[0].str)); }
#line 2103 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 57:
#line 370 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(SYM_T, (yyvsp[0].str)); }
#line 2109 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 58:
#line 372 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = (yyvsp[0].snode); }
#line 2115 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 59:
#line 376 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyvsp[-1].snode_list)->push_back(new ASTNode(NUM_T, (yyvsp[0].str))); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2121 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 60:
#line 378 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); (yyval.snode_list)->push_back(new ASTNode(NUM_T, (yyvsp[0].str))); }
#line 2127 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 61:
#line 382 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = (yyvsp[0].snode); }
#line 2133 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 62:
#line 384 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(AS_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[-2].snode));
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2144 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 63:
#line 393 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
#line 2150 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 64:
#line 395 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2156 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 65:
#line 399 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(VARB_T, (yyvsp[-2].str)); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[-1].snode)); }
#line 2162 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 66:
#line 403 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
#line 2168 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 67:
#line 405 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2174 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 68:
#line 409 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(SV_T, (yyvsp[-2].str));  (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[-1].snode)); }
#line 2180 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 69:
#line 412 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
#line 2186 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 70:
#line 414 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyvsp[-1].snode_list)->push_back((yyvsp[0].snode)); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2192 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 71:
#line 418 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(TERM_T, NULL); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 2198 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 72:
#line 420 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(QID_T, NULL); (yyval.snode)->children = new std::list<ASTNode*>(); (yyval.snode)->children->push_back((yyvsp[0].snode)); }
#line 2204 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 73:
#line 422 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(LQID_T, NULL);
            (yyval.snode)->children = (yyvsp[-1].snode_list);
            (yyval.snode)->children->push_front((yyvsp[-2].snode));
            (yyval.snode)->children->push_front((yyvsp[-3].snode));
        }
#line 2215 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 74:
#line 429 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(LET_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyvsp[-3].snode_list)->push_front((yyvsp[-4].snode));
            ASTNode* vbl = new ASTNode(VARBL_T, NULL);
            vbl->children = (yyvsp[-3].snode_list);
            (yyval.snode)->children->push_back(vbl);
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2229 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 75:
#line 439 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(FORALL_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyvsp[-3].snode_list)->push_front((yyvsp[-4].snode));
            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = (yyvsp[-3].snode_list);
            (yyval.snode)->children->push_back(svl);
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2243 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 76:
#line 449 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(EXISTS_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyvsp[-3].snode_list)->push_front((yyvsp[-4].snode));
            ASTNode* svl = new ASTNode(SVL_T, NULL);
            svl->children = (yyvsp[-3].snode_list);
            (yyval.snode)->children->push_back(svl);
            (yyval.snode)->children->push_back((yyvsp[-1].snode));
        }
#line 2257 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 77:
#line 459 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(BANG_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_front((yyvsp[-3].snode));
            ASTNode *atrs = new ASTNode(GATTRL_T, NULL);
            (yyvsp[-1].snode_list)->push_front((yyvsp[-2].snode));
            atrs->children = (yyvsp[-1].snode_list);
            (yyval.snode)->children->push_back(atrs);
        }
#line 2271 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 78:
#line 535 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode_list) = new std::list<ASTNode*>(); }
#line 2277 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 79:
#line 537 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyvsp[-1].snode_list)->push_back(new ASTNode(SYM_T, (yyvsp[0].str))); (yyval.snode_list) = (yyvsp[-1].snode_list); }
#line 2283 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 80:
#line 694 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
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
#line 2298 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 81:
#line 707 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2308 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 82:
#line 713 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2318 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 83:
#line 719 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2328 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 84:
#line 725 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2338 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 85:
#line 731 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2348 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 86:
#line 737 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2358 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 87:
#line 743 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2368 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 88:
#line 749 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(STR_T, (yyvsp[0].str)));
        }
#line 2378 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 89:
#line 755 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(STR_T, (yyvsp[0].str)));
        }
#line 2388 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 90:
#line 761 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[0].str)));
        }
#line 2398 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 91:
#line 767 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, (yyvsp[-1].str));
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(NUM_T, (yyvsp[0].str)));
        }
#line 2408 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 92:
#line 773 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(OPTION_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back((yyvsp[0].snode));
        }
#line 2418 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 93:
#line 781 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2424 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 94:
#line 783 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2430 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 95:
#line 785 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2436 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 96:
#line 787 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2442 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 97:
#line 789 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2448 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 98:
#line 791 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2454 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 99:
#line 793 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2460 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 100:
#line 795 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2466 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 101:
#line 797 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2472 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 102:
#line 799 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2478 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 103:
#line 801 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2484 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 104:
#line 803 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2490 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 105:
#line 805 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2496 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 106:
#line 807 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2502 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 107:
#line 809 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2508 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 108:
#line 811 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2514 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 109:
#line 813 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2520 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 110:
#line 815 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2526 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 111:
#line 817 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2532 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 112:
#line 819 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2538 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 113:
#line 821 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2544 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 114:
#line 823 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2550 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 115:
#line 825 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2556 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 116:
#line 827 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2562 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 117:
#line 829 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2568 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 118:
#line 831 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2574 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 119:
#line 833 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2580 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 120:
#line 835 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2586 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 121:
#line 837 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.str) = (yyvsp[0].str); }
#line 2592 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 122:
#line 841 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 2598 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 123:
#line 843 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 2604 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 124:
#line 845 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 2610 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 125:
#line 847 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 2616 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 126:
#line 849 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 2622 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 127:
#line 851 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 2628 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 128:
#line 853 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    { (yyval.snode) = new ASTNode(INFO_T, (yyvsp[0].str)); }
#line 2634 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;

  case 129:
#line 855 "smt2new/smt2newparser.yy" /* yacc.c:1646  */
    {
            (yyval.snode) = new ASTNode(INFO_T, NULL);
            (yyval.snode)->children = new std::list<ASTNode*>();
            (yyval.snode)->children->push_back(new ASTNode(GATTR_T, (yyvsp[0].str)));
        }
#line 2644 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
    break;


#line 2648 "smt2new/smt2newparser.cc" /* yacc.c:1646  */
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
#line 862 "smt2new/smt2newparser.yy" /* yacc.c:1906  */


//=======================================================================================
// Auxiliary Routines

