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
#define yyparse smt2parse
#define yylex   smt2lex
#define yyerror smt2error
#define yylval  smt2lval
#define yychar  smt2char
#define yydebug smt2debug
#define yynerrs smt2nerrs


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




/* Copy the first part of user declarations.  */
#line 20 "smt2parser.yy"

#include "Global.h"
#include "Egraph.h"
#include "SStore.h"
#include "ParserTypes.h"
#include "OpenSMTContext.h"
#include <cstdio>
#include <cstdlib>
#include <cassert>

extern int smt2lineno;
extern int smt2lex( );
extern OpenSMTContext * parser_ctx;

vector< string > * createNumeralList  ( const char * );
vector< string > * pushNumeralList    ( vector< string > *, const char * );
void		   destroyNumeralList ( vector< string > * );

list< Snode * > * createSortList  ( Snode * );
list< Snode * > * pushSortList    ( list< Snode * > *, Snode * );
void		  destroySortList ( list< Snode * > * );

list< Anode * > * createAttrList  ( Anode * );
list< Anode * > * pushAttrList    ( list< Anode * > *, Anode * );
void		  destroyAttrList ( list< Anode * > * );

class             SpNode;


void smt2error( const char * s )
{
  printf( "At line %d: %s\n", smt2lineno, s );
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
/* Line 193 of yacc.c.  */
#line 368 "smt2parser.cc"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif



/* Copy the second part of user declarations.  */


/* Line 216 of yacc.c.  */
#line 381 "smt2parser.cc"

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
#define YYFINAL  17
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   260

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  110
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  23
/* YYNRULES -- Number of rules.  */
#define YYNRULES  96
/* YYNRULES -- Number of states.  */
#define YYNSTATES  208

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   361

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
     107,   108,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,   109,     2,     2,     2,     2,
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
      85,    86,    87,    88,    89,    90,    91,    92,    93,    94,
      95,    96,    97,    98,    99,   100,   101,   102,   103,   104,
     105,   106
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     5,     8,    10,    15,    20,    25,    31,
      40,    48,    53,    58,    63,    67,    71,    75,    79,    81,
      83,    85,    87,    89,    91,    93,    95,    97,   103,   105,
     107,   110,   112,   114,   118,   121,   123,   125,   127,   133,
     135,   140,   142,   144,   146,   151,   156,   161,   166,   171,
     176,   181,   186,   191,   196,   201,   206,   211,   216,   221,
     226,   231,   238,   244,   250,   258,   260,   265,   268,   270,
     276,   281,   284,   286,   289,   291,   294,   296,   298,   300,
     302,   304,   307,   310,   313,   316,   319,   322,   325,   328,
     331,   334,   337,   340,   342,   345,   347
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int16 yyrhs[] =
{
     111,     0,    -1,   112,    -1,   112,   113,    -1,   113,    -1,
     107,    11,   117,   108,    -1,   107,    13,   131,   108,    -1,
     107,    12,   118,   108,    -1,   107,    14,   117,   127,   108,
      -1,   107,    16,   117,   107,   122,   108,   120,   108,    -1,
     107,    16,   117,   107,   108,   120,   108,    -1,   107,    17,
     127,   108,    -1,   107,    18,   127,   108,    -1,   107,    36,
     121,   108,    -1,   107,    19,   108,    -1,   107,    21,   108,
      -1,   107,    23,   108,    -1,   107,    28,   108,    -1,   115,
      -1,     7,    -1,     8,    -1,   127,    -1,   128,    -1,   129,
      -1,   130,    -1,     6,    -1,     7,    -1,   107,   109,     7,
     126,   108,    -1,     7,    -1,     8,    -1,     8,   119,    -1,
     115,    -1,     7,    -1,   107,   125,   108,    -1,   107,   108,
      -1,    10,    -1,    38,    -1,    37,    -1,   107,    39,   120,
     120,   108,    -1,   116,    -1,   107,   116,   122,   108,    -1,
     115,    -1,    59,    -1,    60,    -1,   107,    51,   124,   108,
      -1,   107,    52,   124,   108,    -1,   107,    55,   124,   108,
      -1,   107,    53,   124,   108,    -1,   107,    58,   124,   108,
      -1,   107,    46,   124,   108,    -1,   107,    56,   124,   108,
      -1,   107,    40,   124,   108,    -1,   107,    41,   124,   108,
      -1,   107,    42,   124,   108,    -1,   107,    43,   124,   108,
      -1,   107,    44,   124,   108,    -1,   107,    47,   124,   108,
      -1,   107,    48,   124,   108,    -1,   107,    49,   124,   108,
      -1,   107,    50,   124,   108,    -1,   107,    34,   124,   108,
      -1,   107,   104,   121,   121,   121,   108,    -1,   107,   105,
     121,   121,   108,    -1,   107,   106,   121,   121,   108,    -1,
     107,    30,   107,   123,   108,   121,   108,    -1,   116,    -1,
     107,   116,   124,   108,    -1,   122,   120,    -1,   120,    -1,
     123,   107,     7,   121,   108,    -1,   107,     7,   121,   108,
      -1,   121,   124,    -1,   121,    -1,   125,   114,    -1,   114,
      -1,   126,   127,    -1,   127,    -1,     3,    -1,     4,    -1,
       5,    -1,     9,    -1,    92,   132,    -1,    93,   132,    -1,
      94,   132,    -1,    95,   132,    -1,    96,   132,    -1,    97,
     132,    -1,    98,   132,    -1,    99,   132,    -1,   100,     6,
      -1,   101,     6,    -1,   102,     3,    -1,   103,     3,    -1,
       8,    -1,     8,   114,    -1,    59,    -1,    60,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   113,   113,   115,   115,   117,   119,   121,   123,   129,
     136,   144,   146,   148,   150,   156,   158,   171,   175,   177,
     179,   186,   188,   190,   192,   194,   198,   200,   205,   211,
     215,   221,   226,   231,   236,   243,   245,   247,   249,   258,
     260,   271,   276,   278,   280,   282,   284,   286,   288,   290,
     292,   294,   296,   298,   300,   302,   304,   306,   308,   310,
     312,   314,   316,   318,   320,   333,   338,   346,   348,   354,
     356,   360,   362,   366,   368,   372,   374,   378,   380,   382,
     384,   386,   391,   396,   401,   406,   411,   416,   421,   426,
     433,   438,   443,   448,   450,   457,   464
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "TK_NUM", "TK_DEC", "TK_HEX", "TK_STR",
  "TK_SYM", "TK_KEY", "TK_BIN", "TK_BOOL", "TK_SETLOGIC", "TK_SETINFO",
  "TK_SETOPTION", "TK_DECLARESORT", "TK_DEFINESORT", "TK_DECLAREFUN",
  "TK_PUSH", "TK_POP", "TK_CHECKSAT", "TK_GETASSERTIONS", "TK_GETPROOF",
  "TK_GETUNSATCORE", "TK_GETINTERPOLANTS", "TK_GETVALUE",
  "TK_GETASSIGNMENT", "TK_GETOPTION", "TK_GETINFO", "TK_EXIT", "TK_AS",
  "TK_LET", "TK_FORALL", "TK_EXISTS", "TK_ANNOT", "TK_DISTINCT",
  "TK_DEFINEFUN", "TK_ASSERT", "TK_REAL", "TK_INT", "TK_ARRAY", "TK_PLUS",
  "TK_MINUS", "TK_TIMES", "TK_UMINUS", "TK_DIV", "TK_NE", "TK_EQ",
  "TK_LEQ", "TK_GEQ", "TK_LT", "TK_GT", "TK_AND", "TK_OR", "TK_NOT",
  "TK_IFF", "TK_XOR", "TK_ITE", "TK_IFTHENELSE", "TK_IMPLIES", "TK_TRUE",
  "TK_FALSE", "TK_INTERPOLATE", "TK_BVSLT", "TK_BVSGT", "TK_BVSLE",
  "TK_BVSGE", "TK_BVULT", "TK_BVUGT", "TK_BVULE", "TK_BVUGE", "TK_EXTRACT",
  "TK_CONCAT", "TK_BVAND", "TK_BVOR", "TK_BVXOR", "TK_BVNOT", "TK_BVADD",
  "TK_BVNEG", "TK_BVMUL", "TK_BVASHR", "TK_REPEAT", "TK_SIGN_EXTEND",
  "TK_ZERO_EXTEND", "TK_ROTATE_LEFT", "TK_ROTATE_RIGHT", "TK_BVLSHR",
  "TK_BVSHL", "TK_BVSREM", "TK_BVSDIV", "TK_BVSUB", "TK_BVUDIV",
  "TK_BVUREM", "TK_PRINT_SUCCESS", "TK_EXPAND_DEFINITIONS",
  "TK_INTERACTIVE_MODE", "TK_PRODUCE_PROOFS", "TK_PRODUCE_UNSAT_CORES",
  "TK_PRODUCE_INTERPOLANTS", "TK_PRODUCE_MODELS", "TK_PRODUCE_ASSIGNMENTS",
  "TK_REGULAR_OUTPUT_CHANNEL", "TK_DIAGNOSTIC_OUTPUT_CHANNEL",
  "TK_RANDOM_SEED", "TK_VERBOSITY", "TK_STORE", "TK_SELECT", "TK_DIFF",
  "'('", "')'", "'_'", "$accept", "script", "command_list", "command",
  "s_expr", "spec_const", "identifier", "symbol", "attribute",
  "attribute_value", "sort", "term", "sort_list", "var_binding_list",
  "term_list", "s_expr_list", "numeral_list", "numeral", "decimal",
  "hexadecimal", "binary", "option", "b_value", 0
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
     335,   336,   337,   338,   339,   340,   341,   342,   343,   344,
     345,   346,   347,   348,   349,   350,   351,   352,   353,   354,
     355,   356,   357,   358,   359,   360,   361,    40,    41,    95
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,   110,   111,   112,   112,   113,   113,   113,   113,   113,
     113,   113,   113,   113,   113,   113,   113,   113,   114,   114,
     114,   115,   115,   115,   115,   115,   116,   116,   117,   118,
     118,   119,   119,   119,   119,   120,   120,   120,   120,   120,
     120,   121,   121,   121,   121,   121,   121,   121,   121,   121,
     121,   121,   121,   121,   121,   121,   121,   121,   121,   121,
     121,   121,   121,   121,   121,   121,   121,   122,   122,   123,
     123,   124,   124,   125,   125,   126,   126,   127,   128,   129,
     130,   131,   131,   131,   131,   131,   131,   131,   131,   131,
     131,   131,   131,   131,   131,   132,   132
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     2,     1,     4,     4,     4,     5,     8,
       7,     4,     4,     4,     3,     3,     3,     3,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     5,     1,     1,
       2,     1,     1,     3,     2,     1,     1,     1,     5,     1,
       4,     1,     1,     1,     4,     4,     4,     4,     4,     4,
       4,     4,     4,     4,     4,     4,     4,     4,     4,     4,
       4,     6,     5,     5,     7,     1,     4,     2,     1,     5,
       4,     2,     1,     2,     1,     2,     1,     1,     1,     1,
       1,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     1,     2,     1,     1
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,     0,     0,     2,     4,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     1,     3,    28,
       0,    29,     0,    93,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    77,
       0,     0,    14,    15,    16,    17,    78,    79,    25,    26,
      80,    42,    43,     0,    41,    65,     0,    21,    22,    23,
      24,     5,    32,     0,    31,    30,     7,    19,    20,    94,
      18,    95,    96,    81,    82,    83,    84,    85,    86,    87,
      88,    89,    90,    91,    92,     6,     0,     0,    11,    12,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    13,    34,    74,     0,     8,    35,
      37,    36,     0,     0,    39,    68,     0,     0,    72,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,    33,    73,     0,     0,     0,     0,    67,     0,     0,
      71,    60,    51,    52,    53,    54,    55,    49,    56,    57,
      58,    59,    44,    45,    47,    46,    50,    48,     0,     0,
       0,     0,    76,    66,     0,     0,    10,     0,     0,     0,
       0,     0,    62,    63,    27,    75,     0,    40,     9,     0,
       0,     0,    61,    38,    70,     0,    64,    69
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,     3,     4,    69,    54,    55,    20,    22,    65,
     125,   128,   126,   159,   129,   117,   181,    57,    58,    59,
      60,    36,    73
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -73
static const yytype_int16 yypact[] =
{
     -72,   224,    37,   -72,   -73,    33,    47,    93,    33,    33,
      55,    55,   -36,   -29,   -24,   -22,    16,   -73,   -73,   -73,
     -20,    27,   -19,    41,   -32,   -32,   -32,   -32,   -32,   -32,
     -32,   -32,    53,    85,    92,    94,   -12,    55,    -7,   -73,
      -6,    -5,   -73,   -73,   -73,   -73,   -73,   -73,   -73,   -73,
     -73,   -73,   -73,   108,   -73,   -73,     3,   -73,   -73,   -73,
     -73,   -73,   -73,     2,   -73,   -73,   -73,   -73,   -73,   -73,
     -73,   -73,   -73,   -73,   -73,   -73,   -73,   -73,   -73,   -73,
     -73,   -73,   -73,   -73,   -73,   -73,     6,    32,   -73,   -73,
      13,    16,    16,    16,    16,    16,    16,    16,    16,    16,
      16,    16,    16,    16,    16,    16,    16,    16,    16,    16,
      16,     7,   114,    16,   -73,   -73,   -73,     9,   -73,   -73,
     -73,   -73,    17,    75,   -73,   -73,    61,    15,    16,    19,
      21,    25,    35,    38,    39,    57,    59,    62,    63,    67,
      68,    69,    72,    73,    89,    90,    16,    16,    16,    55,
      91,   -73,   -73,    75,    75,    95,    75,   -73,   118,   -56,
     -73,   -73,   -73,   -73,   -73,   -73,   -73,   -73,   -73,   -73,
     -73,   -73,   -73,   -73,   -73,   -73,   -73,   -73,    16,    96,
      97,    -2,   -73,   -73,    75,    71,   -73,    98,    16,   121,
      16,    99,   -73,   -73,   -73,   -73,   100,   -73,   -73,   101,
      16,   102,   -73,   -73,   -73,   103,   -73,   -73
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
     -73,   -73,   -73,   141,   -37,    20,   -49,    45,   -73,   -73,
     -66,   -16,    -9,   -73,   126,   -73,   -73,    -8,   -73,   -73,
     -73,   -73,    36
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -1
static const yytype_uint8 yytable[] =
{
      56,    39,    40,    41,   113,    39,    46,    47,    48,    67,
      68,    50,    39,    46,    47,    48,    67,    68,    50,    39,
      46,    47,    48,    49,    49,    50,   116,    71,    72,    86,
      39,    46,    47,    48,    62,     1,    50,    17,   124,    49,
      19,    64,   119,    70,    39,    46,    47,    48,    67,    68,
      50,   189,   190,    37,    38,    21,   153,   155,    39,    81,
     157,    74,    75,    76,    77,    78,    79,    80,    49,   120,
     121,   119,    42,   154,   124,    51,    52,   124,    49,    43,
     152,   119,    49,    70,    44,   119,    45,   184,    61,    66,
     187,    82,   146,   147,   148,    83,    85,    84,   120,   121,
      87,    23,    88,    89,   124,   124,   194,   124,   120,   121,
     115,   114,   120,   121,   118,    49,   112,   151,   196,   157,
     127,   149,   158,    53,   111,   188,   112,   161,   200,   162,
     178,   179,   180,   163,    63,   124,   124,    70,    90,   122,
     123,   182,    91,   164,    18,   185,   165,   166,    92,    93,
      94,    95,    96,     0,    97,    98,    99,   100,   101,   102,
     103,   104,   191,   105,   106,   167,   107,   168,   122,   156,
     169,   170,   199,   195,   201,   171,   172,   173,   122,   197,
     174,   175,   122,     0,   205,    24,    25,    26,    27,    28,
      29,    30,    31,    32,    33,    34,    35,   176,   177,   183,
       0,     0,     0,   186,   192,   193,   198,   202,   203,   204,
     206,   207,   108,   109,   110,   111,     0,   112,   130,   131,
     132,   133,   134,   135,   136,   137,   138,   139,   140,   141,
     142,   143,   144,   145,     0,     5,     6,     7,     8,   150,
       9,    10,    11,    12,     0,    13,     0,    14,     0,     0,
       0,     0,    15,     0,   160,     0,     0,     0,     0,     0,
      16
};

static const yytype_int16 yycheck[] =
{
      16,     3,    10,    11,    53,     3,     4,     5,     6,     7,
       8,     9,     3,     4,     5,     6,     7,     8,     9,     3,
       4,     5,     6,     7,     7,     9,    63,    59,    60,    37,
       3,     4,     5,     6,     7,   107,     9,     0,    87,     7,
       7,    21,    10,    23,     3,     4,     5,     6,     7,     8,
       9,   107,   108,     8,     9,     8,    39,   123,     3,     6,
     126,    25,    26,    27,    28,    29,    30,    31,     7,    37,
      38,    10,   108,   122,   123,    59,    60,   126,     7,   108,
     117,    10,     7,    63,   108,    10,   108,   153,   108,   108,
     156,     6,   108,   109,   110,     3,   108,     3,    37,    38,
     107,     8,   108,   108,   153,   154,   108,   156,    37,    38,
     108,   108,    37,    38,   108,     7,   109,   108,   184,   185,
     107,     7,   107,   107,   107,     7,   109,   108,     7,   108,
     146,   147,   148,   108,   107,   184,   185,   117,    30,   107,
     108,   149,    34,   108,     3,   154,   108,   108,    40,    41,
      42,    43,    44,    -1,    46,    47,    48,    49,    50,    51,
      52,    53,   178,    55,    56,   108,    58,   108,   107,   108,
     108,   108,   188,   181,   190,   108,   108,   108,   107,   108,
     108,   108,   107,    -1,   200,    92,    93,    94,    95,    96,
      97,    98,    99,   100,   101,   102,   103,   108,   108,   108,
      -1,    -1,    -1,   108,   108,   108,   108,   108,   108,   108,
     108,   108,   104,   105,   106,   107,    -1,   109,    92,    93,
      94,    95,    96,    97,    98,    99,   100,   101,   102,   103,
     104,   105,   106,   107,    -1,    11,    12,    13,    14,   113,
      16,    17,    18,    19,    -1,    21,    -1,    23,    -1,    -1,
      -1,    -1,    28,    -1,   128,    -1,    -1,    -1,    -1,    -1,
      36
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,   107,   111,   112,   113,    11,    12,    13,    14,    16,
      17,    18,    19,    21,    23,    28,    36,     0,   113,     7,
     117,     8,   118,     8,    92,    93,    94,    95,    96,    97,
      98,    99,   100,   101,   102,   103,   131,   117,   117,     3,
     127,   127,   108,   108,   108,   108,     4,     5,     6,     7,
       9,    59,    60,   107,   115,   116,   121,   127,   128,   129,
     130,   108,     7,   107,   115,   119,   108,     7,     8,   114,
     115,    59,    60,   132,   132,   132,   132,   132,   132,   132,
     132,     6,     6,     3,     3,   108,   127,   107,   108,   108,
      30,    34,    40,    41,    42,    43,    44,    46,    47,    48,
      49,    50,    51,    52,    53,    55,    56,    58,   104,   105,
     106,   107,   109,   116,   108,   108,   114,   125,   108,    10,
      37,    38,   107,   108,   116,   120,   122,   107,   121,   124,
     124,   124,   124,   124,   124,   124,   124,   124,   124,   124,
     124,   124,   124,   124,   124,   124,   121,   121,   121,     7,
     124,   108,   114,    39,   116,   120,   108,   120,   107,   123,
     124,   108,   108,   108,   108,   108,   108,   108,   108,   108,
     108,   108,   108,   108,   108,   108,   108,   108,   121,   121,
     121,   126,   127,   108,   120,   122,   108,   120,     7,   107,
     108,   121,   108,   108,   108,   127,   120,   108,   108,   121,
       7,   121,   108,   108,   108,   121,   108,   108
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
        case 5:
#line 118 "smt2parser.yy"
    { parser_ctx->SetLogic( (yyvsp[(3) - (4)].str) ); free( (yyvsp[(3) - (4)].str) ); }
    break;

  case 6:
#line 120 "smt2parser.yy"
    { }
    break;

  case 7:
#line 122 "smt2parser.yy"
    { parser_ctx->SetInfo( (yyvsp[(3) - (4)].anode) ); free( (yyvsp[(3) - (4)].anode) ); }
    break;

  case 8:
#line 124 "smt2parser.yy"
    { parser_ctx->DeclareSort( (yyvsp[(3) - (5)].str), atoi((yyvsp[(4) - (5)].str)) ); free( (yyvsp[(3) - (5)].str) ); free( (yyvsp[(4) - (5)].str) ); }
    break;

  case 9:
#line 130 "smt2parser.yy"
    { 
	   Snode * a = parser_ctx->mkCons( *(yyvsp[(5) - (8)].snode_list) );
	   Snode * s = parser_ctx->mkSort( a );
	   parser_ctx->DeclareFun( (yyvsp[(3) - (8)].str), s, (yyvsp[(7) - (8)].snode) );
	   destroySortList( (yyvsp[(5) - (8)].snode_list) ); free( (yyvsp[(3) - (8)].str) );
	 }
    break;

  case 10:
#line 137 "smt2parser.yy"
    { parser_ctx->DeclareFun( (yyvsp[(3) - (7)].str), NULL, (yyvsp[(6) - (7)].snode) ); free( (yyvsp[(3) - (7)].str) ); }
    break;

  case 11:
#line 145 "smt2parser.yy"
    { parser_ctx->addPush( atoi( (yyvsp[(3) - (4)].str) ) ); free( (yyvsp[(3) - (4)].str) ); }
    break;

  case 12:
#line 147 "smt2parser.yy"
    { parser_ctx->addPop( atoi( (yyvsp[(3) - (4)].str) ) ); free( (yyvsp[(3) - (4)].str) );}
    break;

  case 13:
#line 149 "smt2parser.yy"
    { parser_ctx->addAssert( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 14:
#line 151 "smt2parser.yy"
    { parser_ctx->addCheckSAT( ); }
    break;

  case 15:
#line 157 "smt2parser.yy"
    { parser_ctx->addGetProof( ); }
    break;

  case 16:
#line 159 "smt2parser.yy"
    { parser_ctx->addGetInterpolants( ); }
    break;

  case 17:
#line 172 "smt2parser.yy"
    { parser_ctx->addExit( ); }
    break;

  case 18:
#line 176 "smt2parser.yy"
    { (yyval.anode) = new Anode( (yyvsp[(1) - (1)].spnode)->type, (yyvsp[(1) - (1)].spnode)->value, NULL ); }
    break;

  case 19:
#line 178 "smt2parser.yy"
    { (yyval.anode) = new Anode( AT_SYM, (yyvsp[(1) - (1)].str), NULL ); }
    break;

  case 20:
#line 180 "smt2parser.yy"
    { (yyval.anode) = new Anode( AT_KEY, (yyvsp[(1) - (1)].str), NULL ); }
    break;

  case 21:
#line 187 "smt2parser.yy"
    { (yyval.spnode) = new SpNode( AT_NUM, (yyvsp[(1) - (1)].str) ); }
    break;

  case 22:
#line 189 "smt2parser.yy"
    { (yyval.spnode) = new SpNode( AT_DEC, (yyvsp[(1) - (1)].str) ); }
    break;

  case 23:
#line 191 "smt2parser.yy"
    { (yyval.spnode) = new SpNode( AT_DEC, (yyvsp[(1) - (1)].str) ); }
    break;

  case 24:
#line 193 "smt2parser.yy"
    { (yyval.spnode) = new SpNode( AT_BIN, (yyvsp[(1) - (1)].str) ); }
    break;

  case 25:
#line 195 "smt2parser.yy"
    { (yyval.spnode) = new SpNode( AT_STR, (yyvsp[(1) - (1)].str) ); }
    break;

  case 26:
#line 199 "smt2parser.yy"
    { (yyval.idnode) = new IdNode((yyvsp[(1) - (1)].str), NULL); }
    break;

  case 27:
#line 200 "smt2parser.yy"
    { (yyval.idnode) = new IdNode((yyvsp[(3) - (5)].str), (yyvsp[(4) - (5)].str_list)); }
    break;

  case 28:
#line 206 "smt2parser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 29:
#line 212 "smt2parser.yy"
    {
            (yyval.anode) = new Anode(AT_KEY, (yyvsp[(1) - (1)].str), NULL);
        }
    break;

  case 30:
#line 216 "smt2parser.yy"
    {
            (yyval.anode) = new Anode(AT_KEY, (yyvsp[(1) - (2)].str), (yyvsp[(2) - (2)].anode_list));
        }
    break;

  case 31:
#line 222 "smt2parser.yy"
    {
            Anode* a = new Anode( (yyvsp[(1) - (1)].spnode)->type, (yyvsp[(1) - (1)].spnode)->value, NULL );
            (yyval.anode_list) = createAttrList( a );
        }
    break;

  case 32:
#line 227 "smt2parser.yy"
    {
            Anode* a = new Anode( AT_SYM, (yyvsp[(1) - (1)].str), NULL );
            (yyval.anode_list) = createAttrList( a );
        }
    break;

  case 33:
#line 232 "smt2parser.yy"
    {
            Anode* a = new Anode( AT_NONE, NULL, (yyvsp[(2) - (3)].anode_list) );
            (yyval.anode_list) = createAttrList( a );
        }
    break;

  case 34:
#line 237 "smt2parser.yy"
    {
            Anode* a = new Anode( AT_NONE, NULL, NULL );
            (yyval.anode_list) = createAttrList( a );
        }
    break;

  case 35:
#line 244 "smt2parser.yy"
    { (yyval.snode) = parser_ctx->mkSortBool( ); }
    break;

  case 36:
#line 246 "smt2parser.yy"
    { (yyval.snode) = parser_ctx->mkSortInt( ); }
    break;

  case 37:
#line 248 "smt2parser.yy"
    { (yyval.snode) = parser_ctx->mkSortReal( ); }
    break;

  case 38:
#line 250 "smt2parser.yy"
    {
        IdNode* idNode = new IdNode( "Array", NULL );
        Snode * a = parser_ctx->mkSortVar( idNode );
        (yyval.snode) = parser_ctx->mkSort(
                 parser_ctx->mkCons( a
               , parser_ctx->mkCons( (yyvsp[(3) - (5)].snode)
               , parser_ctx->mkCons( (yyvsp[(4) - (5)].snode) ) ) ) );
      }
    break;

  case 39:
#line 259 "smt2parser.yy"
    { (yyval.snode) = parser_ctx->mkSortVar( (yyvsp[(1) - (1)].idnode) ); free( (yyvsp[(1) - (1)].idnode) ); }
    break;

  case 40:
#line 261 "smt2parser.yy"
    { 
        Snode * s = parser_ctx->mkCons( parser_ctx->mkSortVar( (yyvsp[(2) - (4)].idnode) ) ); 
	(*(yyvsp[(3) - (4)].snode_list)).push_front( s );
	(yyval.snode) = parser_ctx->mkSort( parser_ctx->mkCons( *(yyvsp[(3) - (4)].snode_list) ) );
        free( (yyvsp[(2) - (4)].idnode) ); 
      }
    break;

  case 41:
#line 272 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkNum( (yyvsp[(1) - (1)].spnode)->value ); free( (yyvsp[(1) - (1)].spnode) ); }
    break;

  case 42:
#line 277 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkTrue( ); }
    break;

  case 43:
#line 279 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkFalse( ); }
    break;

  case 44:
#line 281 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkAnd( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 45:
#line 283 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkOr( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 46:
#line 285 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkXor( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 47:
#line 287 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkNot( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 48:
#line 289 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkImplies( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 49:
#line 291 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkEq( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 50:
#line 293 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkIte( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 51:
#line 295 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkPlus( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 52:
#line 297 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkMinus( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 53:
#line 299 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkTimes( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 54:
#line 301 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkUminus( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 55:
#line 303 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkDiv( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 56:
#line 305 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkLeq( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 57:
#line 307 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkGeq( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 58:
#line 309 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkLt( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 59:
#line 311 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkGt( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 60:
#line 313 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkDistinct( (yyvsp[(3) - (4)].enode) ); }
    break;

  case 61:
#line 315 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkStore( (yyvsp[(3) - (6)].enode), (yyvsp[(4) - (6)].enode), (yyvsp[(5) - (6)].enode) ); }
    break;

  case 62:
#line 317 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkSelect( (yyvsp[(3) - (5)].enode), (yyvsp[(4) - (5)].enode) ); }
    break;

  case 63:
#line 319 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkDiff( (yyvsp[(3) - (5)].enode), (yyvsp[(4) - (5)].enode) ); }
    break;

  case 64:
#line 321 "smt2parser.yy"
    { (yyval.enode) = (yyvsp[(6) - (7)].enode); }
    break;

  case 65:
#line 334 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkVar( (yyvsp[(1) - (1)].idnode)->name ); free( (yyvsp[(1) - (1)].idnode) ); }
    break;

  case 66:
#line 339 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkFun( (yyvsp[(2) - (4)].idnode)->name, (yyvsp[(3) - (4)].enode) ); free( (yyvsp[(2) - (4)].idnode) ); }
    break;

  case 67:
#line 347 "smt2parser.yy"
    { (yyval.snode_list) = pushSortList( (yyvsp[(1) - (2)].snode_list), (yyvsp[(2) - (2)].snode) ); }
    break;

  case 68:
#line 349 "smt2parser.yy"
    { (yyval.snode_list) = createSortList( (yyvsp[(1) - (1)].snode) ); }
    break;

  case 69:
#line 355 "smt2parser.yy"
    { parser_ctx->mkBind( (yyvsp[(3) - (5)].str), (yyvsp[(4) - (5)].enode) ); free((yyvsp[(3) - (5)].str)); }
    break;

  case 70:
#line 357 "smt2parser.yy"
    { parser_ctx->mkBind( (yyvsp[(2) - (4)].str), (yyvsp[(3) - (4)].enode) ); free((yyvsp[(2) - (4)].str)); }
    break;

  case 71:
#line 361 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkCons( (yyvsp[(1) - (2)].enode), (yyvsp[(2) - (2)].enode) ); }
    break;

  case 72:
#line 363 "smt2parser.yy"
    { (yyval.enode) = parser_ctx->mkCons( (yyvsp[(1) - (1)].enode) ); }
    break;

  case 73:
#line 367 "smt2parser.yy"
    { (yyval.anode_list) = pushAttrList( (yyvsp[(1) - (2)].anode_list), (yyvsp[(2) - (2)].anode) ); }
    break;

  case 74:
#line 369 "smt2parser.yy"
    { (yyval.anode_list) = createAttrList( (yyvsp[(1) - (1)].anode) ); }
    break;

  case 75:
#line 373 "smt2parser.yy"
    { (yyval.str_list) = pushNumeralList( (yyvsp[(1) - (2)].str_list), (yyvsp[(2) - (2)].str) ); }
    break;

  case 76:
#line 375 "smt2parser.yy"
    { (yyval.str_list) = createNumeralList( (yyvsp[(1) - (1)].str) ); }
    break;

  case 77:
#line 378 "smt2parser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 78:
#line 380 "smt2parser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 79:
#line 382 "smt2parser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 80:
#line 384 "smt2parser.yy"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 81:
#line 387 "smt2parser.yy"
    { 
	  parser_ctx->SetOption( ":print-success", (yyvsp[(2) - (2)].str) );
	  free( (yyvsp[(2) - (2)].str) );
        }
    break;

  case 82:
#line 392 "smt2parser.yy"
    {
	  parser_ctx->SetOption( ":expand-definitions", (yyvsp[(2) - (2)].str) );
          free( (yyvsp[(2) - (2)].str) );
        }
    break;

  case 83:
#line 397 "smt2parser.yy"
    {
	  parser_ctx->SetOption( ":interactive-mode", (yyvsp[(2) - (2)].str) );
          free( (yyvsp[(2) - (2)].str) );
        }
    break;

  case 84:
#line 402 "smt2parser.yy"
    {
	  parser_ctx->SetOption( ":produce-proofs", (yyvsp[(2) - (2)].str) );
          free( (yyvsp[(2) - (2)].str) );
        }
    break;

  case 85:
#line 407 "smt2parser.yy"
    {
	  parser_ctx->SetOption( ":produce-unsat-cores", (yyvsp[(2) - (2)].str) );
          free( (yyvsp[(2) - (2)].str) );
        }
    break;

  case 86:
#line 412 "smt2parser.yy"
    {
	  parser_ctx->SetOption( ":produce-interpolants", (yyvsp[(2) - (2)].str) );
          free( (yyvsp[(2) - (2)].str) );
        }
    break;

  case 87:
#line 417 "smt2parser.yy"
    {
	  parser_ctx->SetOption( ":produce-models", (yyvsp[(2) - (2)].str) );
          free( (yyvsp[(2) - (2)].str) );
        }
    break;

  case 88:
#line 422 "smt2parser.yy"
    {
	  parser_ctx->SetOption( ":produce-assignments", (yyvsp[(2) - (2)].str) );
          free( (yyvsp[(2) - (2)].str) );
        }
    break;

  case 89:
#line 427 "smt2parser.yy"
    {
	  char buf[256] = ":regular-output-channel "; 
	  strcat( buf, (yyvsp[(2) - (2)].str) );
	  parser_ctx->SetOption( ":regular-output-channel", (yyvsp[(2) - (2)].str) );
          free( (yyvsp[(2) - (2)].str) );
        }
    break;

  case 90:
#line 434 "smt2parser.yy"
    {
	  parser_ctx->SetOption( ":diagnostic-output-channel", (yyvsp[(2) - (2)].str) );
          free( (yyvsp[(2) - (2)].str) );
        }
    break;

  case 91:
#line 439 "smt2parser.yy"
    {
	  parser_ctx->SetOption( ":random-seed", (yyvsp[(2) - (2)].str) );
          free( (yyvsp[(2) - (2)].str) );
        }
    break;

  case 92:
#line 444 "smt2parser.yy"
    {
	  parser_ctx->SetOption( ":verbosity", (yyvsp[(2) - (2)].str) );
          free( (yyvsp[(2) - (2)].str) );
	}
    break;

  case 93:
#line 449 "smt2parser.yy"
    { parser_ctx->SetOption( (yyvsp[(1) - (1)].str) ); free( (yyvsp[(1) - (1)].str) ); }
    break;

  case 94:
#line 451 "smt2parser.yy"
    { 
	  parser_ctx->SetOption( (yyvsp[(1) - (2)].str), (yyvsp[(2) - (2)].anode)->value ); 
	  free( (yyvsp[(1) - (2)].str) ); free( (yyvsp[(2) - (2)].anode) ); 
        }
    break;

  case 95:
#line 458 "smt2parser.yy"
    { 
           char * buf;
           buf = (char *)malloc(sizeof(char) * 10);
	   strcpy( buf, "true" );
	   (yyval.str) = buf;
         }
    break;

  case 96:
#line 465 "smt2parser.yy"
    {
           char * buf;
           buf = (char *)malloc(sizeof(char) * 10);
	   strcpy( buf, "false" );
	   (yyval.str) = buf;
	 }
    break;


/* Line 1267 of yacc.c.  */
#line 2336 "smt2parser.cc"
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


#line 473 "smt2parser.yy"


//=======================================================================================
// Auxiliary Routines

vector< string > * createNumeralList( const char * s )
{
  vector< string > * l = new vector< string >;
  l->push_back( s );
  return l;
} 

vector< string > * pushNumeralList( vector< string > * l, const char * s )
{
  l->push_back( s );
  return l;
}

void destroyNumeralList( vector< string > * l )
{
  delete l;
}

list< Snode * > * createSortList( Snode * s )
{
  list< Snode * > * l = new list< Snode * >;
  l->push_back( s );
  return l;
} 

list< Snode * > * pushSortList( list< Snode * > * l, Snode * s )
{
  l->push_back( s );
  return l;
}

void destroySortList( list< Snode * > * l )
{
  assert( l );
  delete l;
}

list< Anode * > * createAttrList( Anode * a )
{
  list< Anode * > * l = new list< Anode * >;
  l->push_back( a );
  return l;
} 

list< Anode * > * pushAttrList( list< Anode * > * l, Anode * a )
{
  l->push_back( a );
  return l;
}

void destroyAttrList( list< Anode * > * l )
{
  assert( l );
  delete l;
}

