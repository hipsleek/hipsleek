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
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* Copy the first part of user declarations.  */
#line 1 "../src/parser.y" /* yacc.c:339  */


#define compilingParser
#include <basic/Dynamic_Array.h>
#include <code_gen/code_gen.h>
#include <code_gen/spmd.h>
#include <omega/library_version.h>
#include <omega/AST.h>
#include <omega_calc/yylex.h>
#include <omega/hull.h>
#include <omega/calc_debug.h>
#include <basic/Exit.h>
#include <omega/closure.h>
#include <omega/reach.h>
#include <code_gen/mmap-codegen.h>
#include <code_gen/mmap-util.h>
#ifndef WIN32
#include <sys/time.h>
#include <sys/resource.h>
#endif

#define CALC_VERSION_STRING "Omega Calculator v2.1.6"
#define YY_STDINIT
#define DEBUG_FILE_NAME "./oc.out"

/* Can only do the following when "using namespace omega"
   is also put before the inclusion of y.tab.h in parser.l.
*/
using omega::min;
using omega::negate;
using namespace omega;

Map<Const_String,Relation*> relationMap ((Relation *)0);
static int redundant_conj_level;

#if defined BRAIN_DAMAGED_FREE
void free(void *p);
void *realloc(void *p, size_t s);
#endif

namespace omega {
#if !defined(OMIT_GETRUSAGE)
void start_clock( void );
int clock_diff( void );
bool anyTimingDone = false;
#endif

int argCount = 0;
int tuplePos = 0;
Argument_Tuple currentTuple = Input_Tuple;

Relation LexForward(int n);
} // end namespace omega

reachable_information *reachable_info;



#line 125 "y.tab.c" /* yacc.c:339  */

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
# define YYERROR_VERBOSE 0
#endif

/* In a future release of Bison, this section will be replaced
   by #include "y.tab.h".  */
#ifndef YY_YY_Y_TAB_H_INCLUDED
# define YY_YY_Y_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    VAR = 258,
    INT = 259,
    STRING = 260,
    OPEN_BRACE = 261,
    CLOSE_BRACE = 262,
    SYMBOLIC = 263,
    OR = 264,
    AND = 265,
    NOT = 266,
    ST = 267,
    APPROX = 268,
    IS_ASSIGNED = 269,
    FORALL = 270,
    EXISTS = 271,
    OMEGA_DOMAIN = 272,
    RANGE = 273,
    DIFFERENCE = 274,
    DIFFERENCE_TO_RELATION = 275,
    GIST = 276,
    GIVEN = 277,
    HULL = 278,
    WITHIN = 279,
    MAXIMIZE = 280,
    MINIMIZE = 281,
    AFFINE_HULL = 282,
    VENN = 283,
    CONVEX_COMBINATION = 284,
    POSITIVE_COMBINATION = 285,
    CONVEX_HULL = 286,
    CONIC_HULL = 287,
    LINEAR_HULL = 288,
    PAIRWISE_CHECK = 289,
    CONVEX_CHECK = 290,
    MAXIMIZE_RANGE = 291,
    MINIMIZE_RANGE = 292,
    MAXIMIZE_DOMAIN = 293,
    MINIMIZE_DOMAIN = 294,
    LEQ = 295,
    GEQ = 296,
    NEQ = 297,
    GOES_TO = 298,
    COMPOSE = 299,
    JOIN = 300,
    INVERSE = 301,
    COMPLEMENT = 302,
    IN = 303,
    CARRIED_BY = 304,
    TIME = 305,
    TIMECLOSURE = 306,
    UNION = 307,
    INTERSECTION = 308,
    VERTICAL_BAR = 309,
    SUCH_THAT = 310,
    SUBSET = 311,
    ITERATIONS = 312,
    SPMD = 313,
    CODEGEN = 314,
    DECOUPLED_FARKAS = 315,
    FARKAS = 316,
    TCODEGEN = 317,
    TRANS_IS = 318,
    SET_MMAP = 319,
    UNROLL_IS = 320,
    PEEL_IS = 321,
    MAKE_UPPER_BOUND = 322,
    MAKE_LOWER_BOUND = 323,
    REL_OP = 324,
    RESTRICT_DOMAIN = 325,
    RESTRICT_RANGE = 326,
    SUPERSETOF = 327,
    SUBSETOF = 328,
    SAMPLE = 329,
    SYM_SAMPLE = 330,
    PROJECT_AWAY_SYMBOLS = 331,
    PROJECT_ON_SYMBOLS = 332,
    REACHABLE_FROM = 333,
    REACHABLE_OF = 334,
    ASSERT_UNSAT = 335,
    PARSE_EXPRESSION = 336,
    PARSE_FORMULA = 337,
    PARSE_RELATION = 338,
    p1 = 339,
    p2 = 340,
    p3 = 341,
    p4 = 342,
    p5 = 343,
    p6 = 344,
    p7 = 345,
    p8 = 346,
    p9 = 347,
    p10 = 348
  };
#endif
/* Tokens.  */
#define VAR 258
#define INT 259
#define STRING 260
#define OPEN_BRACE 261
#define CLOSE_BRACE 262
#define SYMBOLIC 263
#define OR 264
#define AND 265
#define NOT 266
#define ST 267
#define APPROX 268
#define IS_ASSIGNED 269
#define FORALL 270
#define EXISTS 271
#define OMEGA_DOMAIN 272
#define RANGE 273
#define DIFFERENCE 274
#define DIFFERENCE_TO_RELATION 275
#define GIST 276
#define GIVEN 277
#define HULL 278
#define WITHIN 279
#define MAXIMIZE 280
#define MINIMIZE 281
#define AFFINE_HULL 282
#define VENN 283
#define CONVEX_COMBINATION 284
#define POSITIVE_COMBINATION 285
#define CONVEX_HULL 286
#define CONIC_HULL 287
#define LINEAR_HULL 288
#define PAIRWISE_CHECK 289
#define CONVEX_CHECK 290
#define MAXIMIZE_RANGE 291
#define MINIMIZE_RANGE 292
#define MAXIMIZE_DOMAIN 293
#define MINIMIZE_DOMAIN 294
#define LEQ 295
#define GEQ 296
#define NEQ 297
#define GOES_TO 298
#define COMPOSE 299
#define JOIN 300
#define INVERSE 301
#define COMPLEMENT 302
#define IN 303
#define CARRIED_BY 304
#define TIME 305
#define TIMECLOSURE 306
#define UNION 307
#define INTERSECTION 308
#define VERTICAL_BAR 309
#define SUCH_THAT 310
#define SUBSET 311
#define ITERATIONS 312
#define SPMD 313
#define CODEGEN 314
#define DECOUPLED_FARKAS 315
#define FARKAS 316
#define TCODEGEN 317
#define TRANS_IS 318
#define SET_MMAP 319
#define UNROLL_IS 320
#define PEEL_IS 321
#define MAKE_UPPER_BOUND 322
#define MAKE_LOWER_BOUND 323
#define REL_OP 324
#define RESTRICT_DOMAIN 325
#define RESTRICT_RANGE 326
#define SUPERSETOF 327
#define SUBSETOF 328
#define SAMPLE 329
#define SYM_SAMPLE 330
#define PROJECT_AWAY_SYMBOLS 331
#define PROJECT_ON_SYMBOLS 332
#define REACHABLE_FROM 333
#define REACHABLE_OF 334
#define ASSERT_UNSAT 335
#define PARSE_EXPRESSION 336
#define PARSE_FORMULA 337
#define PARSE_RELATION 338
#define p1 339
#define p2 340
#define p3 341
#define p4 342
#define p5 343
#define p6 344
#define p7 345
#define p8 346
#define p9 347
#define p10 348

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE YYSTYPE;
union YYSTYPE
{
#line 130 "../src/parser.y" /* yacc.c:355  */

	int INT_VALUE;
	Rel_Op REL_OPERATOR;
	char *VAR_NAME;
	VarList *VAR_LIST;
	Exp *EXP;
	ExpList *EXP_LIST;
	AST *ASTP;
	Argument_Tuple ARGUMENT_TUPLE;
	AST_constraints *ASTCP;
	Declaration_Site * DECLARATION_SITE;
	Relation * RELATION;
	tupleDescriptor * TUPLE_DESCRIPTOR;
	RelTuplePair * REL_TUPLE_PAIR;
        RelTupleTriple * REL_TUPLE_TRIPLE;
	Dynamic_Array2<Relation> * RELATION_ARRAY_2D;
	Dynamic_Array1<Relation> * RELATION_ARRAY_1D;
	Tuple<String> *STRING_TUPLE;
	String *STRING_VALUE;
  	Tuple<stm_info> *STM_INFO_TUPLE;
  	stm_info *STM_INFO;
	Read *READ;
	PartialRead *PREAD;
	MMap *MMAP;
	PartialMMap *PMMAP;
	

#line 379 "y.tab.c" /* yacc.c:355  */
};
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;

int yyparse (void);

#endif /* !YY_YY_Y_TAB_H_INCLUDED  */

/* Copy the second part of user declarations.  */

#line 394 "y.tab.c" /* yacc.c:358  */

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
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

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
#define YYLAST   891

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  105
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  54
/* YYNRULES -- Number of rules.  */
#define YYNRULES  180
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  372

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   348

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
      97,   104,    89,    85,   100,    86,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,   101,    99,
       2,     2,     2,     2,    90,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,   102,     2,   103,     2,     2,     2,     2,     2,     2,
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
      87,    88,    91,    92,    93,    94,    95,    96,    98
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   161,   161,   161,   165,   166,   166,   171,   183,   186,
     195,   203,   288,   379,   387,   396,   415,   444,   466,   476,
     489,   490,   491,   492,   495,   496,   497,   500,   502,   505,
     515,   524,   535,   547,   554,   558,   562,   564,   568,   575,
     578,   583,   589,   597,   601,   606,   612,   619,   622,   627,
     630,   633,   638,   644,   645,   648,   650,   655,   654,   667,
     679,   680,   685,   692,   698,   707,   716,   725,   734,   744,
     754,   760,   766,   771,   776,   781,   786,   791,   796,   801,
     807,   812,   817,   822,   827,   832,   837,   842,   847,   852,
     858,   863,   868,   873,   878,   884,   890,   896,   902,   908,
     914,   920,   926,   932,   938,   944,   949,   954,   959,   964,
     969,   974,   975,   989,   990,   989,  1016,  1033,  1042,  1043,
    1046,  1047,  1048,  1052,  1052,  1058,  1059,  1060,  1063,  1077,
    1079,  1081,  1083,  1088,  1089,  1093,  1103,  1104,  1107,  1108,
    1109,  1110,  1111,  1112,  1114,  1118,  1119,  1122,  1123,  1124,
    1127,  1128,  1131,  1134,  1138,  1143,  1149,  1151,  1156,  1162,
    1162,  1174,  1180,  1192,  1205,  1206,  1207,  1208,  1209,  1210,
    1211,  1216,  1225,  1240,  1248,  1251,  1257,  1310,  1318,  1329,
    1340
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 0
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "VAR", "INT", "STRING", "OPEN_BRACE",
  "CLOSE_BRACE", "SYMBOLIC", "OR", "AND", "NOT", "ST", "APPROX",
  "IS_ASSIGNED", "FORALL", "EXISTS", "OMEGA_DOMAIN", "RANGE", "DIFFERENCE",
  "DIFFERENCE_TO_RELATION", "GIST", "GIVEN", "HULL", "WITHIN", "MAXIMIZE",
  "MINIMIZE", "AFFINE_HULL", "VENN", "CONVEX_COMBINATION",
  "POSITIVE_COMBINATION", "CONVEX_HULL", "CONIC_HULL", "LINEAR_HULL",
  "PAIRWISE_CHECK", "CONVEX_CHECK", "MAXIMIZE_RANGE", "MINIMIZE_RANGE",
  "MAXIMIZE_DOMAIN", "MINIMIZE_DOMAIN", "LEQ", "GEQ", "NEQ", "GOES_TO",
  "COMPOSE", "JOIN", "INVERSE", "COMPLEMENT", "IN", "CARRIED_BY", "TIME",
  "TIMECLOSURE", "UNION", "INTERSECTION", "VERTICAL_BAR", "SUCH_THAT",
  "SUBSET", "ITERATIONS", "SPMD", "CODEGEN", "DECOUPLED_FARKAS", "FARKAS",
  "TCODEGEN", "TRANS_IS", "SET_MMAP", "UNROLL_IS", "PEEL_IS",
  "MAKE_UPPER_BOUND", "MAKE_LOWER_BOUND", "REL_OP", "RESTRICT_DOMAIN",
  "RESTRICT_RANGE", "SUPERSETOF", "SUBSETOF", "SAMPLE", "SYM_SAMPLE",
  "PROJECT_AWAY_SYMBOLS", "PROJECT_ON_SYMBOLS", "REACHABLE_FROM",
  "REACHABLE_OF", "ASSERT_UNSAT", "PARSE_EXPRESSION", "PARSE_FORMULA",
  "PARSE_RELATION", "p1", "'+'", "'-'", "p2", "p3", "'*'", "'@'", "p4",
  "p5", "p6", "p7", "p8", "p9", "'('", "p10", "';'", "','", "':'", "'['",
  "']'", "')'", "$accept", "start", "$@1", "inputSequence", "$@2",
  "inputItem", "relTripList", "blockAndProcsAndEffort", "effort",
  "context", "relPairList", "statementInfoResult", "statementInfoList",
  "statementInfo", "partialwrites", "partialwrite", "reads", "oneread",
  "partials", "partial", "globVarList", "globVar", "relation", "$@3",
  "builtRelation", "$@4", "$@5", "optionalFormula", "formula_sep",
  "tupleDeclaration", "$@6", "optionalTupleVarList", "tupleVar", "varList",
  "varDecl", "varDeclOptBrackets", "formula", "start_exists", "exists_sep",
  "start_forall", "forall_sep", "end_quant", "expList", "constraintChain",
  "simpleExp", "$@7", "argumentList", "exp", "reachable", "reachable_of",
  "nodeNameList", "realNodeNameList", "nodeSpecificationList",
  "realNodeSpecificationList", YY_NULLPTR
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
     325,   326,   327,   328,   329,   330,   331,   332,   333,   334,
     335,   336,   337,   338,   339,    43,    45,   340,   341,    42,
      64,   342,   343,   344,   345,   346,   347,    40,   348,    59,
      44,    58,    91,    93,    41
};
# endif

#define YYPACT_NINF -252

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-252)))

#define YYTABLE_NINF -129

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
    -252,    64,   336,  -252,    -9,    78,  -252,    97,   164,   164,
     164,   164,   164,   164,   164,   164,   164,   164,   164,   164,
     164,   164,   164,   164,   164,   164,   164,   164,   164,   164,
     164,   164,   164,   164,   101,    42,   164,   164,    42,   164,
     164,   164,   164,   164,   164,   164,   164,    47,   143,   164,
     164,   151,  -252,   631,    60,  -252,  -252,   164,    51,    79,
     -21,  -252,  -252,    89,    89,    89,    89,    89,   205,     4,
      89,    89,    89,    35,    89,    89,    89,    89,    89,    89,
      89,    89,    89,    89,    89,    89,    89,   661,   691,   168,
     164,  -252,   184,   164,    89,    89,    33,    89,    89,   794,
     794,    89,    89,    89,    89,   201,   202,   173,   781,   218,
     336,   164,   164,   222,   164,   164,   164,   164,   164,   206,
     164,   164,  -252,   164,  -252,  -252,   721,   132,    45,    51,
     136,   145,    72,    57,   244,   180,   150,   121,    27,    27,
     191,  -252,  -252,   227,   249,  -252,    97,   164,   164,   164,
    -252,  -252,   262,   115,   466,  -252,    34,   490,   164,   264,
     268,   275,   280,   258,   186,  -252,  -252,   -11,   284,  -252,
      47,  -252,  -252,    89,    89,  -252,   794,    39,   751,   220,
     220,   164,    39,    39,   373,  -252,  -252,    72,  -252,  -252,
    -252,  -252,  -252,   136,   145,    41,    75,  -252,  -252,  -252,
    -252,  -252,  -252,    51,    66,    51,    51,  -252,   289,   193,
    -252,    26,   195,    72,    72,    72,    72,    72,   207,  -252,
      89,    89,    89,  -252,  -252,   164,   164,   164,   164,   215,
     164,   431,   300,   302,   314,   221,   225,   224,   326,  -252,
      15,    38,   202,  -252,    89,  -252,   328,   170,  -252,  -252,
    -252,   121,   -26,  -252,    53,  -252,   127,   322,  -252,   230,
     333,  -252,  -252,  -252,    51,  -252,    51,   191,  -252,   251,
     251,  -252,  -252,  -252,   513,   537,   781,   560,  -252,   781,
    -252,   -37,   182,  -252,   334,   164,   164,  -252,  -252,  -252,
     338,   164,  -252,   342,  -252,  -252,    14,  -252,    66,  -252,
      72,  -252,  -252,    43,    43,   164,   164,   164,   164,   164,
     300,  -252,    33,   403,   607,   245,   781,    48,   345,  -252,
      32,  -252,   234,  -252,  -252,  -252,   584,   781,   781,   781,
     375,  -252,  -252,   164,  -252,   300,   164,   347,   164,  -252,
    -252,   348,   164,   260,   431,    65,   781,   250,   781,  -252,
     781,   164,  -252,    22,  -252,   164,   781,   372,    71,  -252,
     781,   277,   106,  -252,   276,  -252,   164,   372,  -252,  -252,
     781,  -252
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       2,     0,     0,     1,     0,    59,    57,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    20,    24,     0,     0,    24,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     5,     4,     0,     0,   111,     7,     0,   123,    56,
       0,    54,    59,    90,    77,    91,    75,    76,     0,    88,
      68,    69,    85,    78,    82,    81,    80,    86,    87,    83,
      84,    65,    64,    67,    66,    92,    93,     0,     0,    21,
       0,    25,     0,     0,    71,    70,     0,   107,   108,   105,
     106,   109,   110,    73,    74,     0,     0,     0,   112,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    61,
       0,    62,    72,     0,    10,    17,     0,   158,   164,     0,
       0,     0,     0,     0,     0,   119,     0,   117,     0,     0,
       0,   140,   166,   155,     0,     8,     0,     0,     0,     0,
      11,    12,    22,     0,     0,    26,    27,    32,     0,     0,
       0,     0,     0,    27,    33,    39,   175,     0,     0,   171,
       0,    60,     6,    96,    98,    97,   103,   101,     0,   100,
      99,     0,   102,   104,     0,     9,   159,     0,   165,   142,
     151,   146,   167,   150,   145,     0,   155,    58,   113,   121,
     122,   120,   116,     0,   127,     0,     0,   134,     0,   135,
     136,     0,     0,     0,     0,     0,     0,     0,     0,    53,
      94,    89,    79,    23,    16,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   173,
       0,     0,     0,    13,    63,    95,     0,     0,   141,   161,
     123,   118,   158,   129,     0,   125,   130,   139,   138,     0,
       0,   148,   149,   147,     0,   152,     0,   156,   157,   168,
     169,   170,   154,    55,     0,     0,    28,    30,    14,    31,
      34,     0,     0,    44,     0,     0,     0,    15,    40,   174,
       0,     0,   176,     0,   172,   163,     0,   114,     0,   124,
       0,   137,   133,     0,     0,     0,     0,     0,     0,     0,
       0,    35,     0,     0,     0,     0,   180,     0,     0,   160,
     119,   126,   131,   153,   143,   144,     0,    19,    29,    46,
       0,    43,    36,     0,    37,     0,     0,     0,     0,   162,
     115,     0,     0,     0,     0,     0,   179,     0,   177,   132,
      18,     0,    38,     0,    42,     0,    45,     0,     0,    48,
     178,     0,     0,    51,     0,    41,     0,     0,    49,    47,
      52,    50
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -252,  -252,  -252,  -252,  -252,   269,  -252,  -252,   343,   217,
    -252,  -187,  -252,   147,    50,  -251,  -252,    24,  -252,    23,
    -252,   243,    -8,  -252,  -252,  -252,  -252,    73,  -252,   141,
    -252,  -252,    94,  -252,   192,   263,   -86,  -252,  -252,  -252,
    -252,    95,   -51,   188,   278,  -252,  -252,   -93,  -252,  -252,
     235,  -252,   165,  -252
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     1,     2,    51,   110,    52,   153,    90,    93,   229,
     156,   163,   164,   165,   282,   283,   358,   359,   362,   363,
      60,    61,    53,    58,   134,   250,   320,   202,   203,   135,
     136,   254,   255,   209,   210,   211,   137,   138,   264,   139,
     266,   324,   140,   141,   142,   246,   296,   143,    54,    55,
     106,   167,   169,   241
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
      63,    64,    65,    66,    67,    68,    69,    70,    71,    72,
      73,    74,    75,    76,    77,    78,    79,    80,    81,    82,
      83,    84,    85,    86,    87,    88,   148,   281,    94,    95,
     207,    97,    98,    99,   100,   101,   102,   103,   104,   192,
     196,   108,   109,   189,   280,   292,    91,   195,   127,   126,
     205,   206,   205,   206,   127,   128,   227,   149,   290,   331,
     127,   128,   129,   308,     3,   309,   130,   131,   129,   252,
     128,   186,   193,   194,  -128,   127,   128,  -128,   145,   146,
     261,   262,   154,   111,   112,   157,   199,   200,   113,   238,
      56,   337,    57,   239,   247,   311,   158,   159,   160,   161,
      59,   123,   331,   173,   174,    89,   176,   177,   178,   179,
     180,   256,   182,   183,   318,   184,   291,   251,   319,   257,
     258,   269,   270,   271,   357,   332,   334,   263,    92,   208,
     205,   206,   123,   201,   228,   162,   123,   132,   293,   220,
     221,   222,   187,   132,   105,   248,   107,   323,   133,   338,
     231,    -3,   132,   298,   133,   253,   299,   352,   132,   125,
     214,   215,   267,   187,   216,   353,   272,    62,   354,   187,
       6,   364,   152,   244,   365,   217,   144,     8,   303,   249,
     304,     9,    10,    11,    12,    13,   123,    14,   155,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    27,    28,    29,   166,   256,   367,   322,   168,   368,
      30,    31,   214,   215,   224,   225,   216,   274,   275,   276,
     277,   170,   279,   198,    36,    37,   175,   147,   300,   186,
     181,    39,    40,   190,   199,   200,    41,    42,    43,    44,
      45,    46,   191,    48,    49,   158,   159,   160,   161,   111,
     112,   197,   204,   218,   113,   214,   215,   114,   115,   216,
     213,    50,   111,   112,   111,   112,   223,   113,   232,   113,
     114,   115,   233,   115,   249,   117,   118,   313,   314,   234,
     227,   201,   310,   316,   162,   235,   237,   240,   117,   118,
     119,   120,   207,   260,   121,   122,   265,   326,   327,   328,
     329,   330,   123,   119,   120,   281,   284,   121,   122,   121,
     122,   273,   214,   215,   278,   123,   216,   123,   285,   214,
     215,   286,   171,   216,   287,   344,   162,   217,   346,   289,
     348,   295,   206,   301,   350,   341,   302,     4,   312,     5,
     216,   315,     6,   356,     7,   317,   336,   360,   339,     8,
     347,   355,   349,     9,    10,    11,    12,    13,   370,    14,
     351,    15,    16,    17,    18,    19,    20,    21,    22,    23,
      24,    25,    26,    27,    28,    29,   361,   366,   357,   172,
     236,    96,    30,    31,   288,   345,    32,    33,   369,   219,
     371,   297,   321,   340,    34,    35,    36,    37,    38,   325,
     259,   268,   212,    39,    40,   242,   188,   294,    41,    42,
      43,    44,    45,    46,    47,    48,    49,   111,   112,   111,
     112,     0,   113,     0,   113,   114,   115,   114,   115,     0,
       0,     0,     0,    50,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   117,   118,   117,   118,   111,   112,     0,
       0,     0,   113,     0,     0,   114,   115,     0,   119,   120,
     119,   120,   121,   122,   121,   122,   158,   159,   160,   161,
     123,     0,   123,   117,   118,   111,   112,   245,   343,     0,
     113,     0,     0,   114,   115,     0,     0,     0,   119,   120,
       0,     0,   121,   122,   158,   159,   160,   161,     0,     0,
     123,   117,   118,   333,     0,   162,     0,     0,     0,     0,
     111,   112,     0,     0,     0,   113,   119,   120,   114,   115,
     121,   122,     0,     0,     0,     0,     0,     0,   123,     0,
       0,     0,     0,   162,   111,   112,   117,   118,     0,   113,
       0,     0,   114,   115,     0,     0,     0,     0,     0,     0,
       0,   119,   120,     0,     0,   121,   122,   111,   112,     0,
     117,   118,   113,   123,     0,   114,   115,   226,     0,     0,
       0,     0,     0,     0,     0,   119,   120,     0,     0,   121,
     122,   111,   112,   117,   118,     0,   113,   123,     0,   114,
     115,   230,     0,     0,     0,     0,     0,     0,   119,   120,
       0,     0,   121,   122,   111,   112,     0,   117,   118,   113,
     123,     0,   114,   115,   305,     0,     0,     0,     0,     0,
       0,     0,   119,   120,     0,     0,   121,   122,   111,   112,
     117,   118,     0,   113,   123,     0,   114,   115,   306,     0,
       0,     0,     0,     0,     0,   119,   120,     0,     0,   121,
     122,   111,   112,     0,   117,   118,   113,   123,     0,   114,
     115,   307,     0,     0,     0,     0,     0,     0,     0,   119,
     120,     0,     0,   121,   122,   111,   112,   117,   118,     0,
     113,   123,     0,   114,   115,   342,     0,   116,     0,     0,
       0,     0,   119,   120,     0,     0,   121,   122,     0,     0,
       0,   117,   118,     0,   123,   111,   112,   335,     0,     0,
     113,     0,     0,   114,   115,     0,   119,   120,     0,     0,
     121,   122,     0,     0,     0,     0,     0,     0,   123,     0,
     124,   117,   118,     0,     0,   111,   112,     0,     0,     0,
     113,     0,     0,   114,   115,     0,   119,   120,     0,     0,
     121,   122,     0,     0,     0,     0,     0,     0,   123,     0,
     150,   117,   118,     0,     0,   111,   112,     0,     0,     0,
     113,     0,     0,   114,   115,     0,   119,   120,     0,     0,
     121,   122,     0,     0,     0,     0,     0,     0,   123,     0,
     151,   117,   118,     0,     0,   111,   112,     0,     0,     0,
     113,     0,     0,   114,   115,     0,   119,   120,     0,     0,
     121,   122,     0,     0,     0,     0,     0,     0,   123,     0,
     185,   117,   118,     0,     0,   111,   112,     0,     0,     0,
     113,     0,     0,   114,   115,     0,   119,   120,   111,   112,
     121,   122,     0,   113,     0,     0,     0,   115,   123,     0,
     243,   117,   118,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   117,   118,   119,   120,     0,     0,
     121,   122,     0,     0,     0,     0,     0,     0,   123,     0,
       0,     0,     0,   121,   122,     0,     0,     0,     0,     0,
       0,   123
};

static const yytype_int16 yycheck[] =
{
       8,     9,    10,    11,    12,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    25,    26,    27,
      28,    29,    30,    31,    32,    33,    22,     5,    36,    37,
       3,    39,    40,    41,    42,    43,    44,    45,    46,   132,
     133,    49,    50,   129,   231,     7,     4,   133,     3,    57,
       9,    10,     9,    10,     3,     4,    22,    22,    43,   310,
       3,     4,    11,   100,     0,   102,    15,    16,    11,     3,
       4,    97,    15,    16,   100,     3,     4,   103,    99,   100,
      54,    55,    90,    44,    45,    93,    54,    55,    49,   100,
      99,    43,    14,   104,   187,   282,    63,    64,    65,    66,
       3,    97,   353,   111,   112,     4,   114,   115,   116,   117,
     118,   204,   120,   121,   100,   123,   101,   203,   104,   205,
     206,   214,   215,   216,   102,   312,   313,   101,    86,   102,
       9,    10,    97,   101,   100,   102,    97,    86,   100,   147,
     148,   149,    97,    86,    97,   104,     3,   104,    97,   101,
     158,     0,    86,   100,    97,    89,   103,   344,    86,    99,
      85,    86,   213,    97,    89,   100,   217,     3,   103,    97,
       6,   100,     4,   181,   103,   100,    97,    13,   264,   104,
     266,    17,    18,    19,    20,    21,    97,    23,     4,    25,
      26,    27,    28,    29,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,     3,   298,   100,   300,     6,   103,
      46,    47,    85,    86,    99,   100,    89,   225,   226,   227,
     228,    48,   230,    43,    60,    61,     4,    22,   101,    97,
      24,    67,    68,    97,    54,    55,    72,    73,    74,    75,
      76,    77,    97,    79,    80,    63,    64,    65,    66,    44,
      45,     7,   102,     4,    49,    85,    86,    52,    53,    89,
      69,    97,    44,    45,    44,    45,     4,    49,     4,    49,
      52,    53,     4,    53,   104,    70,    71,   285,   286,     4,
      22,   101,   100,   291,   102,     5,   100,     3,    70,    71,
      85,    86,     3,   100,    89,    90,   101,   305,   306,   307,
     308,   309,    97,    85,    86,     5,     4,    89,    90,    89,
      90,   104,    85,    86,    99,    97,    89,    97,     4,    85,
      86,   100,   104,    89,    99,   333,   102,   100,   336,     3,
     338,     3,    10,   103,   342,   101,     3,     1,     4,     3,
      89,     3,     6,   351,     8,     3,   101,   355,     3,    13,
       3,   101,     4,    17,    18,    19,    20,    21,   366,    23,
     100,    25,    26,    27,    28,    29,    30,    31,    32,    33,
      34,    35,    36,    37,    38,    39,     4,   100,   102,   110,
     163,    38,    46,    47,   237,   335,    50,    51,   364,   146,
     367,   250,   298,   320,    58,    59,    60,    61,    62,   304,
     208,   213,   139,    67,    68,   170,   128,   242,    72,    73,
      74,    75,    76,    77,    78,    79,    80,    44,    45,    44,
      45,    -1,    49,    -1,    49,    52,    53,    52,    53,    -1,
      -1,    -1,    -1,    97,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    70,    71,    70,    71,    44,    45,    -1,
      -1,    -1,    49,    -1,    -1,    52,    53,    -1,    85,    86,
      85,    86,    89,    90,    89,    90,    63,    64,    65,    66,
      97,    -1,    97,    70,    71,    44,    45,   104,   103,    -1,
      49,    -1,    -1,    52,    53,    -1,    -1,    -1,    85,    86,
      -1,    -1,    89,    90,    63,    64,    65,    66,    -1,    -1,
      97,    70,    71,   100,    -1,   102,    -1,    -1,    -1,    -1,
      44,    45,    -1,    -1,    -1,    49,    85,    86,    52,    53,
      89,    90,    -1,    -1,    -1,    -1,    -1,    -1,    97,    -1,
      -1,    -1,    -1,   102,    44,    45,    70,    71,    -1,    49,
      -1,    -1,    52,    53,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    85,    86,    -1,    -1,    89,    90,    44,    45,    -1,
      70,    71,    49,    97,    -1,    52,    53,   101,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    85,    86,    -1,    -1,    89,
      90,    44,    45,    70,    71,    -1,    49,    97,    -1,    52,
      53,   101,    -1,    -1,    -1,    -1,    -1,    -1,    85,    86,
      -1,    -1,    89,    90,    44,    45,    -1,    70,    71,    49,
      97,    -1,    52,    53,   101,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    85,    86,    -1,    -1,    89,    90,    44,    45,
      70,    71,    -1,    49,    97,    -1,    52,    53,   101,    -1,
      -1,    -1,    -1,    -1,    -1,    85,    86,    -1,    -1,    89,
      90,    44,    45,    -1,    70,    71,    49,    97,    -1,    52,
      53,   101,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    85,
      86,    -1,    -1,    89,    90,    44,    45,    70,    71,    -1,
      49,    97,    -1,    52,    53,   101,    -1,    56,    -1,    -1,
      -1,    -1,    85,    86,    -1,    -1,    89,    90,    -1,    -1,
      -1,    70,    71,    -1,    97,    44,    45,   100,    -1,    -1,
      49,    -1,    -1,    52,    53,    -1,    85,    86,    -1,    -1,
      89,    90,    -1,    -1,    -1,    -1,    -1,    -1,    97,    -1,
      99,    70,    71,    -1,    -1,    44,    45,    -1,    -1,    -1,
      49,    -1,    -1,    52,    53,    -1,    85,    86,    -1,    -1,
      89,    90,    -1,    -1,    -1,    -1,    -1,    -1,    97,    -1,
      99,    70,    71,    -1,    -1,    44,    45,    -1,    -1,    -1,
      49,    -1,    -1,    52,    53,    -1,    85,    86,    -1,    -1,
      89,    90,    -1,    -1,    -1,    -1,    -1,    -1,    97,    -1,
      99,    70,    71,    -1,    -1,    44,    45,    -1,    -1,    -1,
      49,    -1,    -1,    52,    53,    -1,    85,    86,    -1,    -1,
      89,    90,    -1,    -1,    -1,    -1,    -1,    -1,    97,    -1,
      99,    70,    71,    -1,    -1,    44,    45,    -1,    -1,    -1,
      49,    -1,    -1,    52,    53,    -1,    85,    86,    44,    45,
      89,    90,    -1,    49,    -1,    -1,    -1,    53,    97,    -1,
      99,    70,    71,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    70,    71,    85,    86,    -1,    -1,
      89,    90,    -1,    -1,    -1,    -1,    -1,    -1,    97,    -1,
      -1,    -1,    -1,    89,    90,    -1,    -1,    -1,    -1,    -1,
      -1,    97
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,   106,   107,     0,     1,     3,     6,     8,    13,    17,
      18,    19,    20,    21,    23,    25,    26,    27,    28,    29,
      30,    31,    32,    33,    34,    35,    36,    37,    38,    39,
      46,    47,    50,    51,    58,    59,    60,    61,    62,    67,
      68,    72,    73,    74,    75,    76,    77,    78,    79,    80,
      97,   108,   110,   127,   153,   154,    99,    14,   128,     3,
     125,   126,     3,   127,   127,   127,   127,   127,   127,   127,
     127,   127,   127,   127,   127,   127,   127,   127,   127,   127,
     127,   127,   127,   127,   127,   127,   127,   127,   127,     4,
     112,     4,    86,   113,   127,   127,   113,   127,   127,   127,
     127,   127,   127,   127,   127,    97,   155,     3,   127,   127,
     109,    44,    45,    49,    52,    53,    56,    70,    71,    85,
      86,    89,    90,    97,    99,    99,   127,     3,     4,    11,
      15,    16,    86,    97,   129,   134,   135,   141,   142,   144,
     147,   148,   149,   152,    97,    99,   100,    22,    22,    22,
      99,    99,     4,   111,   127,     4,   115,   127,    63,    64,
      65,    66,   102,   116,   117,   118,     3,   156,     6,   157,
      48,   104,   110,   127,   127,     4,   127,   127,   127,   127,
     127,    24,   127,   127,   127,    99,    97,    97,   149,   141,
      97,    97,   152,    15,    16,   141,   152,     7,    43,    54,
      55,   101,   132,   133,   102,     9,    10,     3,   102,   138,
     139,   140,   140,    69,    85,    86,    89,   100,     4,   126,
     127,   127,   127,     4,    99,   100,   101,    22,   100,   114,
     101,   127,     4,     4,     4,     5,   114,   100,   100,   104,
       3,   158,   155,    99,   127,   104,   150,   152,   104,   104,
     130,   141,     3,    89,   136,   137,   152,   141,   141,   139,
     100,    54,    55,   101,   143,   101,   145,   147,   148,   152,
     152,   152,   147,   104,   127,   127,   127,   127,    99,   127,
     116,     5,   119,   120,     4,     4,   100,    99,   118,     3,
      43,   101,     7,   100,   157,     3,   151,   134,   100,   103,
     101,   103,     3,   141,   141,   101,   101,   101,   100,   102,
     100,   116,     4,   127,   127,     3,   127,     3,   100,   104,
     131,   137,   152,   104,   146,   146,   127,   127,   127,   127,
     127,   120,   116,   100,   116,   100,   101,    43,   101,     3,
     132,   101,   101,   103,   127,   119,   127,     3,   127,     4,
     127,   100,   116,   100,   103,   101,   127,   102,   121,   122,
     127,     4,   123,   124,   100,   103,   100,   100,   103,   122,
     127,   124
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,   105,   107,   106,   108,   109,   108,   110,   110,   110,
     110,   110,   110,   110,   110,   110,   110,   110,   111,   111,
     112,   112,   112,   112,   113,   113,   113,   114,   114,   115,
     115,   115,   115,   116,   116,   116,   116,   116,   116,   117,
     117,   118,   118,   119,   119,   120,   120,   121,   121,   122,
     123,   123,   124,   125,   125,   126,   126,   128,   127,   127,
     127,   127,   127,   127,   127,   127,   127,   127,   127,   127,
     127,   127,   127,   127,   127,   127,   127,   127,   127,   127,
     127,   127,   127,   127,   127,   127,   127,   127,   127,   127,
     127,   127,   127,   127,   127,   127,   127,   127,   127,   127,
     127,   127,   127,   127,   127,   127,   127,   127,   127,   127,
     127,   127,   127,   130,   131,   129,   129,   129,   132,   132,
     133,   133,   133,   135,   134,   136,   136,   136,   137,   137,
     137,   137,   137,   138,   138,   139,   140,   140,   141,   141,
     141,   141,   141,   141,   141,   142,   142,   143,   143,   143,
     144,   144,   145,   146,   147,   147,   148,   148,   149,   150,
     149,   149,   151,   151,   152,   152,   152,   152,   152,   152,
     152,   153,   154,   155,   156,   156,   157,   158,   158,   158,
     158
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     0,     2,     1,     0,     3,     2,     3,     4,
       2,     3,     3,     4,     5,     5,     4,     2,     7,     5,
       0,     1,     2,     3,     0,     1,     2,     0,     2,     5,
       3,     3,     1,     1,     3,     4,     5,     5,     7,     1,
       3,     9,     7,     3,     1,     6,     3,     3,     1,     3,
       3,     1,     3,     3,     1,     4,     1,     0,     4,     1,
       3,     2,     2,     4,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     4,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     4,
       2,     2,     2,     2,     4,     4,     3,     3,     3,     3,
       3,     3,     3,     3,     3,     2,     2,     2,     2,     2,
       2,     1,     2,     0,     0,     6,     2,     1,     2,     0,
       1,     1,     1,     0,     4,     1,     3,     0,     1,     1,
       1,     3,     5,     3,     1,     1,     1,     3,     3,     3,
       1,     3,     2,     5,     5,     2,     2,     1,     1,     1,
       2,     2,     1,     1,     3,     1,     3,     3,     1,     0,
       5,     3,     3,     1,     1,     2,     1,     2,     3,     3,
       3,     3,     5,     3,     3,     1,     3,     5,     7,     5,
       3
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
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256



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

/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
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
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
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
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, int yyrule)
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
                                              );
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule); \
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
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
{
  YYUSE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Number of syntax errors so far.  */
int yynerrs;


/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.

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

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
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
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
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
      yychar = yylex ();
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


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 161 "../src/parser.y" /* yacc.c:1646  */
    { 
        }
#line 1860 "y.tab.c" /* yacc.c:1646  */
    break;

  case 5:
#line 166 "../src/parser.y" /* yacc.c:1646  */
    { assert( current_Declaration_Site == globalDecls);}
#line 1866 "y.tab.c" /* yacc.c:1646  */
    break;

  case 7:
#line 171 "../src/parser.y" /* yacc.c:1646  */
    {
		flushScanBuffer();
		/* Kill all the local declarations -- ejr */
		Declaration_Site *ds1, *ds2;
		for(ds1 = current_Declaration_Site; ds1 != globalDecls;) {
		    ds2 = ds1;
		    ds1=ds1->previous;
		    delete ds2;
		}
                current_Declaration_Site = globalDecls;
		yyerror("skipping to statement end");
		}
#line 1883 "y.tab.c" /* yacc.c:1646  */
    break;

  case 8:
#line 184 "../src/parser.y" /* yacc.c:1646  */
    { flushScanBuffer();
		}
#line 1890 "y.tab.c" /* yacc.c:1646  */
    break;

  case 9:
#line 187 "../src/parser.y" /* yacc.c:1646  */
    {
			  flushScanBuffer();
			  (yyvsp[-1].RELATION)->simplify(::min(2,redundant_conj_level),4);
			  Relation *r = relationMap((Const_String)(yyvsp[-3].VAR_NAME));
			  if (r) delete r;
			  relationMap[(Const_String)(yyvsp[-3].VAR_NAME)] = (yyvsp[-1].RELATION); 
			  delete (yyvsp[-3].VAR_NAME);
			}
#line 1903 "y.tab.c" /* yacc.c:1646  */
    break;

  case 10:
#line 195 "../src/parser.y" /* yacc.c:1646  */
    { 
			  flushScanBuffer();
			printf("\n"); 
			(yyvsp[-1].RELATION)->simplify(redundant_conj_level,4);
			(yyvsp[-1].RELATION)->print_with_subs(stdout); 
			printf("\n"); 
			delete (yyvsp[-1].RELATION);
			}
#line 1916 "y.tab.c" /* yacc.c:1646  */
    break;

  case 11:
#line 203 "../src/parser.y" /* yacc.c:1646  */
    {

#if defined(OMIT_GETRUSAGE)
	    printf("'time' requires getrusage, but the omega calclator was compiled with OMIT_GETRUSAGE set!\n");

#else

			flushScanBuffer();
			printf("\n");
			int t;
			Relation R;
			bool SKIP_FULL_CHECK = getenv("OC_TIMING_SKIP_FULL_CHECK");
			((yyvsp[-1].RELATION))->and_with_GEQ();
			start_clock();
			for (t=1;t<=100;t++) {
				R = *(yyvsp[-1].RELATION);
				R.finalize();
				}
			int copyTime = clock_diff();
			start_clock();
			for (t=1;t<=100;t++) {
				R = *(yyvsp[-1].RELATION);
				R.finalize();
				R.simplify();
				}
			int simplifyTime = clock_diff() -copyTime;
			Relation R2;
			if (!SKIP_FULL_CHECK)
			  {
			    start_clock();
			    for (t=1;t<=100;t++) {
			      R2 = *(yyvsp[-1].RELATION);
			      R2.finalize();
			      R2.simplify(2,4);
			    }
			  }
			int excessiveTime = clock_diff() - copyTime;
			printf("Times (in microseconds): \n");
			printf("%5d us to copy original set of constraints\n",copyTime/100);
			printf("%5d us to do the default amount of simplification, obtaining: \n\t",
					simplifyTime/100);
			R.print_with_subs(stdout); 
		    printf("\n"); 
			if (!SKIP_FULL_CHECK)
			  {
			    printf("%5d us to do the maximum (i.e., excessive) amount of simplification, obtaining: \n\t",
				   excessiveTime/100);
			    R2.print_with_subs(stdout); 
			    printf("\n");
			  }
			if (!anyTimingDone) {
				bool warn = false;
#ifndef SPEED 
				warn =true;
#endif
#ifndef NDEBUG
				warn = true;
#endif
				if (warn) {
				   printf("WARNING: The Omega calculator was compiled with options that force\n");
				   printf("it to perform additional consistency and error checks\n");
				   printf("that may slow it down substantially\n");
				  printf("\n");
				   }
				printf("NOTE: These times relect the time of the current _implementation_\n");
				printf("of our algorithms. Performance bugs do exist. If you intend to publish or \n");
				printf("report on the performance on the Omega test, we respectfully but strongly \n");
				printf("request that send your test cases to us to allow us to determine if the \n");
				printf("times are appropriate, and if the way you are using the Omega library to \n"); 
				printf("solve your problem is the most effective way.\n");
				printf("\n");

printf("Also, please be aware that over the past two years, we have focused our \n");
printf("efforts on the expressive power of the Omega library, sometimes at the\n");
printf("expensive of raw speed. Our original implementation of the Omega test\n");
printf("was substantially faster on the limited domain it handled.\n");
				printf("\n");
				printf("	Thanks, \n");
				printf("	   the Omega Team \n");	
				
				}			 
			anyTimingDone = true;
			delete (yyvsp[-1].RELATION);
#endif
			}
#line 2006 "y.tab.c" /* yacc.c:1646  */
    break;

  case 12:
#line 288 "../src/parser.y" /* yacc.c:1646  */
    {

#if defined(OMIT_GETRUSAGE)
	    printf("'timeclosure' requires getrusage, but the omega calclator was compiled with OMIT_GETRUSAGE set!\n");
#else
			flushScanBuffer();
			printf("\n");
			
			int t;
			Relation R;
			((yyvsp[-1].RELATION))->and_with_GEQ();
			start_clock();
			for (t=1;t<=100;t++) {
				R = *(yyvsp[-1].RELATION);
				R.finalize();
				}
			int copyTime = clock_diff();
			start_clock();
			for (t=1;t<=100;t++) {
				R = *(yyvsp[-1].RELATION);
				R.finalize();
				R.simplify();
				};
			int simplifyTime = clock_diff() -copyTime;
			Relation Rclosed;
			start_clock();
			for (t=1;t<=100;t++) {
				Rclosed = *(yyvsp[-1].RELATION);
				Rclosed.finalize();
				Rclosed = TransitiveClosure(Rclosed, 1,Relation::Null());
				};
			int closureTime = clock_diff() - copyTime;
			Relation R2;
			start_clock();
			for (t=1;t<=100;t++) {
				R2 = *(yyvsp[-1].RELATION);
				R2.finalize();
				R2.simplify(2,4);
				};
			int excessiveTime = clock_diff() - copyTime;
			printf("Times (in microseconds): \n");
			printf("%5d us to copy original set of constraints\n",copyTime/100);
			printf("%5d us to do the default amount of simplification, obtaining: \n\t",
					simplifyTime/100);
			R.print_with_subs(stdout); 
		    printf("\n"); 
			printf("%5d us to do the maximum (i.e., excessive) amount of simplification, obtaining: \n\t",
					excessiveTime/100);
			R2.print_with_subs(stdout); 
			printf("%5d us to do the transitive closure, obtaining: \n\t",
					closureTime/100);
			Rclosed.print_with_subs(stdout);
		        printf("\n");
				
			if (!anyTimingDone) {
				bool warn = false;
#ifndef SPEED 
				warn =true;
#endif
#ifndef NDEBUG
				warn = true;
#endif
				if (warn) {
				   printf("WARNING: The Omega calculator was compiled with options that force\n");
				   printf("it to perform additional consistency and error checks\n");
				   printf("that may slow it down substantially\n");
				  printf("\n");
				   }
				printf("NOTE: These times relect the time of the current _implementation_\n");
				printf("of our algorithms. Performance bugs do exist. If you intend to publish or \n");
				printf("report on the performance on the Omega test, we respectfully but strongly \n");
				printf("request that send your test cases to us to allow us to determine if the \n");
				printf("times are appropriate, and if the way you are using the Omega library to \n"); 
				printf("solve your problem is the most effective way.\n");
				printf("\n");

printf("Also, please be aware that over the past two years, we have focused our \n");
printf("efforts on the expressive power of the Omega library, sometimes at the\n");
printf("expensive of raw speed. Our original implementation of the Omega test\n");
printf("was substantially faster on the limited domain it handled.\n");
				printf("\n");
				printf("	Thanks, \n");
				printf("	   the Omega Team \n");	
				
				}			 
			anyTimingDone = true;
			delete (yyvsp[-1].RELATION);
#endif
			}
#line 2100 "y.tab.c" /* yacc.c:1646  */
    break;

  case 13:
#line 379 "../src/parser.y" /* yacc.c:1646  */
    {
			  flushScanBuffer();
	                int c = Must_Be_Subset(*(yyvsp[-3].RELATION), *(yyvsp[-1].RELATION));
			printf("\n%s\n", c ? "True" : "False");
			
			delete (yyvsp[-3].RELATION);
			delete (yyvsp[-1].RELATION);
			}
#line 2113 "y.tab.c" /* yacc.c:1646  */
    break;

  case 14:
#line 388 "../src/parser.y" /* yacc.c:1646  */
    {
			  flushScanBuffer();
			  String s = MMGenerateCode((yyvsp[-2].REL_TUPLE_PAIR)->mappings, (yyvsp[-2].REL_TUPLE_PAIR)->ispaces,*(yyvsp[-1].RELATION),(yyvsp[-3].INT_VALUE));
			  delete (yyvsp[-1].RELATION);
			  delete (yyvsp[-2].REL_TUPLE_PAIR);
			  printf("%s\n", (const char *) s); 
			  
	               }
#line 2126 "y.tab.c" /* yacc.c:1646  */
    break;

  case 15:
#line 397 "../src/parser.y" /* yacc.c:1646  */
    {
			  flushScanBuffer();
			  String s = tcodegen((yyvsp[-3].INT_VALUE), *((yyvsp[-2].STM_INFO_TUPLE)), *((yyvsp[-1].RELATION)));
			  delete (yyvsp[-1].RELATION);
			  delete (yyvsp[-2].STM_INFO_TUPLE);
			  printf("%s\n", (const char *) s); 
			 
			}
#line 2139 "y.tab.c" /* yacc.c:1646  */
    break;

  case 16:
#line 416 "../src/parser.y" /* yacc.c:1646  */
    {
	    Tuple<Free_Var_Decl*> lowerBounds(0), upperBounds(0), my_procs(0);
            Tuple<spmd_stmt_info *> names(0);

	    flushScanBuffer();
	    int nr_statements = (yyvsp[-1].REL_TUPLE_TRIPLE)->space.size();

	    for (int i = 1; i<= (yyvsp[-1].REL_TUPLE_TRIPLE)->space[1].n_out(); i++)
		{
	        lowerBounds.append(new Free_Var_Decl("lb" + itoS(i)));
	        upperBounds.append(new Free_Var_Decl("ub" + itoS(i)));
	        my_procs.append(new Free_Var_Decl("my_proc" + itoS(i)));
		}

            for (int p = 1; p <= nr_statements; p++)
                names.append(new numbered_stmt_info(p-1, Identity((yyvsp[-1].REL_TUPLE_TRIPLE)->time[p].n_out()),
					            (yyvsp[-1].REL_TUPLE_TRIPLE)->space[p], 
					(char *)(const char *)("s"+itoS(p-1))));

	    String s = SPMD_GenerateCode("", (yyvsp[-1].REL_TUPLE_TRIPLE)->space, (yyvsp[-1].REL_TUPLE_TRIPLE)->time, (yyvsp[-1].REL_TUPLE_TRIPLE)->ispaces, 
					 names,
					 lowerBounds, upperBounds, my_procs,
                                         nr_statements);

	    delete (yyvsp[-1].REL_TUPLE_TRIPLE);
	    printf("%s\n", (const char *) s); 
		
            }
#line 2172 "y.tab.c" /* yacc.c:1646  */
    break;

  case 17:
#line 445 "../src/parser.y" /* yacc.c:1646  */
    { 	flushScanBuffer();
		Dynamic_Array1<Relation> &final = *(yyvsp[-1].RELATION_ARRAY_1D);
		bool any_sat=false;
		int i,n_nodes = reachable_info->node_names.size();
		for(i = 1; i <= n_nodes; i++) if(final[i].is_upper_bound_satisfiable()) {
		  any_sat = true;
		  fprintf(stdout,"Node %s: ",
			  (const char *) (reachable_info->node_names[i]));
		  final[i].print_with_subs(stdout);
		  
		}
		if(!any_sat)
		{
		  fprintf(stdout,"No nodes reachable.\n");
		  
		}
		delete (yyvsp[-1].RELATION_ARRAY_1D);
		delete reachable_info;
	}
#line 2196 "y.tab.c" /* yacc.c:1646  */
    break;

  case 18:
#line 467 "../src/parser.y" /* yacc.c:1646  */
    {
                (yyvsp[-6].REL_TUPLE_TRIPLE)->space.append(*(yyvsp[-4].RELATION));
                (yyvsp[-6].REL_TUPLE_TRIPLE)->time.append(*(yyvsp[-2].RELATION));
                (yyvsp[-6].REL_TUPLE_TRIPLE)->ispaces.append(*(yyvsp[0].RELATION));
                delete (yyvsp[-4].RELATION);
                delete (yyvsp[-2].RELATION);
                delete (yyvsp[0].RELATION);
                (yyval.REL_TUPLE_TRIPLE) = (yyvsp[-6].REL_TUPLE_TRIPLE);
                }
#line 2210 "y.tab.c" /* yacc.c:1646  */
    break;

  case 19:
#line 477 "../src/parser.y" /* yacc.c:1646  */
    {
                RelTupleTriple *rtt = new RelTupleTriple;
                rtt->space.append(*(yyvsp[-4].RELATION));
                rtt->time.append(*(yyvsp[-2].RELATION));
                rtt->ispaces.append(*(yyvsp[0].RELATION));
                delete (yyvsp[-4].RELATION);
                delete (yyvsp[-2].RELATION);
                delete (yyvsp[0].RELATION);
                (yyval.REL_TUPLE_TRIPLE) = rtt;
                }
#line 2225 "y.tab.c" /* yacc.c:1646  */
    break;

  case 20:
#line 489 "../src/parser.y" /* yacc.c:1646  */
    { Block_Size = 0; Num_Procs = 0; overheadEffort=0; }
#line 2231 "y.tab.c" /* yacc.c:1646  */
    break;

  case 21:
#line 490 "../src/parser.y" /* yacc.c:1646  */
    { Block_Size = (yyvsp[0].INT_VALUE); Num_Procs = 0; overheadEffort=0;}
#line 2237 "y.tab.c" /* yacc.c:1646  */
    break;

  case 22:
#line 491 "../src/parser.y" /* yacc.c:1646  */
    { Block_Size = (yyvsp[-1].INT_VALUE); Num_Procs = (yyvsp[0].INT_VALUE); overheadEffort=0;}
#line 2243 "y.tab.c" /* yacc.c:1646  */
    break;

  case 23:
#line 492 "../src/parser.y" /* yacc.c:1646  */
    { Block_Size = (yyvsp[-2].INT_VALUE); Num_Procs = (yyvsp[-1].INT_VALUE); overheadEffort=(yyvsp[0].INT_VALUE);}
#line 2249 "y.tab.c" /* yacc.c:1646  */
    break;

  case 24:
#line 495 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.INT_VALUE) = 0; }
#line 2255 "y.tab.c" /* yacc.c:1646  */
    break;

  case 25:
#line 496 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.INT_VALUE) = (yyvsp[0].INT_VALUE); }
#line 2261 "y.tab.c" /* yacc.c:1646  */
    break;

  case 26:
#line 497 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.INT_VALUE) = -(yyvsp[0].INT_VALUE); }
#line 2267 "y.tab.c" /* yacc.c:1646  */
    break;

  case 27:
#line 500 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		*(yyval.RELATION) = Relation::Null(); }
#line 2274 "y.tab.c" /* yacc.c:1646  */
    break;

  case 28:
#line 502 "../src/parser.y" /* yacc.c:1646  */
    {(yyval.RELATION) = (yyvsp[0].RELATION); }
#line 2280 "y.tab.c" /* yacc.c:1646  */
    break;

  case 29:
#line 506 "../src/parser.y" /* yacc.c:1646  */
    {
	        (yyvsp[-4].REL_TUPLE_PAIR)->mappings.append(*(yyvsp[-2].RELATION));
		(yyvsp[-4].REL_TUPLE_PAIR)->mappings[(yyvsp[-4].REL_TUPLE_PAIR)->mappings.size()].compress();
		(yyvsp[-4].REL_TUPLE_PAIR)->ispaces.append(*(yyvsp[0].RELATION));
		(yyvsp[-4].REL_TUPLE_PAIR)->ispaces[(yyvsp[-4].REL_TUPLE_PAIR)->ispaces.size()].compress();
		delete (yyvsp[-2].RELATION);
		delete (yyvsp[0].RELATION);
	        (yyval.REL_TUPLE_PAIR) = (yyvsp[-4].REL_TUPLE_PAIR);
                }
#line 2294 "y.tab.c" /* yacc.c:1646  */
    break;

  case 30:
#line 516 "../src/parser.y" /* yacc.c:1646  */
    {
	        (yyvsp[-2].REL_TUPLE_PAIR)->mappings.append(Identity((yyvsp[0].RELATION)->n_set()));
		(yyvsp[-2].REL_TUPLE_PAIR)->mappings[(yyvsp[-2].REL_TUPLE_PAIR)->mappings.size()].compress();
		(yyvsp[-2].REL_TUPLE_PAIR)->ispaces.append(*(yyvsp[0].RELATION));
		(yyvsp[-2].REL_TUPLE_PAIR)->ispaces[(yyvsp[-2].REL_TUPLE_PAIR)->ispaces.size()].compress();
		delete (yyvsp[0].RELATION);
	        (yyval.REL_TUPLE_PAIR) = (yyvsp[-2].REL_TUPLE_PAIR);
                }
#line 2307 "y.tab.c" /* yacc.c:1646  */
    break;

  case 31:
#line 525 "../src/parser.y" /* yacc.c:1646  */
    {
                RelTuplePair *rtp = new RelTuplePair;
	        rtp->mappings.append(*(yyvsp[-2].RELATION));
		rtp->mappings[rtp->mappings.size()].compress();
	        rtp->ispaces.append(*(yyvsp[0].RELATION));
		rtp->ispaces[rtp->ispaces.size()].compress();
		delete (yyvsp[-2].RELATION);
		delete (yyvsp[0].RELATION);
	        (yyval.REL_TUPLE_PAIR) = rtp;
		}
#line 2322 "y.tab.c" /* yacc.c:1646  */
    break;

  case 32:
#line 536 "../src/parser.y" /* yacc.c:1646  */
    {
                RelTuplePair *rtp = new RelTuplePair;
	        rtp->mappings.append(Identity((yyvsp[0].RELATION)->n_set()));
		rtp->mappings[rtp->mappings.size()].compress();
	        rtp->ispaces.append(*(yyvsp[0].RELATION));
		rtp->ispaces[rtp->ispaces.size()].compress();
		delete (yyvsp[0].RELATION);
	        (yyval.REL_TUPLE_PAIR) = rtp;
                }
#line 2336 "y.tab.c" /* yacc.c:1646  */
    break;

  case 33:
#line 548 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.STM_INFO_TUPLE) = (yyvsp[0].STM_INFO_TUPLE); }
#line 2342 "y.tab.c" /* yacc.c:1646  */
    break;

  case 34:
#line 555 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.STM_INFO_TUPLE) = &Trans_IS(*((yyvsp[0].STM_INFO_TUPLE)), *((yyvsp[-1].RELATION)));
		  delete (yyvsp[-1].RELATION);
		}
#line 2350 "y.tab.c" /* yacc.c:1646  */
    break;

  case 35:
#line 559 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.STM_INFO_TUPLE) = &Set_MMap(*((yyvsp[0].STM_INFO_TUPLE)), (yyvsp[-2].INT_VALUE), *((yyvsp[-1].MMAP)));
		  delete (yyvsp[-1].MMAP);
		}
#line 2358 "y.tab.c" /* yacc.c:1646  */
    break;

  case 36:
#line 563 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.STM_INFO_TUPLE) = &Unroll_One_IS(*((yyvsp[0].STM_INFO_TUPLE)), (yyvsp[-3].INT_VALUE), (yyvsp[-2].INT_VALUE), (yyvsp[-1].INT_VALUE));}
#line 2364 "y.tab.c" /* yacc.c:1646  */
    break;

  case 37:
#line 565 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.STM_INFO_TUPLE) = &Peel_One_IS(*((yyvsp[0].STM_INFO_TUPLE)), (yyvsp[-3].INT_VALUE), (yyvsp[-2].INT_VALUE), *((yyvsp[-1].RELATION)));
		  delete (yyvsp[-1].RELATION);
		}
#line 2372 "y.tab.c" /* yacc.c:1646  */
    break;

  case 38:
#line 569 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.STM_INFO_TUPLE) = &Peel_One_IS(*((yyvsp[0].STM_INFO_TUPLE)), (yyvsp[-5].INT_VALUE), (yyvsp[-4].INT_VALUE), *((yyvsp[-3].RELATION)), *((yyvsp[-1].RELATION)));
		  delete (yyvsp[-3].RELATION);
		  delete (yyvsp[-1].RELATION);
		}
#line 2381 "y.tab.c" /* yacc.c:1646  */
    break;

  case 39:
#line 575 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.STM_INFO_TUPLE) = new Tuple<stm_info>;
						  (yyval.STM_INFO_TUPLE)->append(*((yyvsp[0].STM_INFO)));
						  delete (yyvsp[0].STM_INFO); }
#line 2389 "y.tab.c" /* yacc.c:1646  */
    break;

  case 40:
#line 578 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.STM_INFO_TUPLE) = (yyvsp[-2].STM_INFO_TUPLE);
						  (yyval.STM_INFO_TUPLE)->append(*((yyvsp[0].STM_INFO)));
						  delete (yyvsp[0].STM_INFO); }
#line 2397 "y.tab.c" /* yacc.c:1646  */
    break;

  case 41:
#line 584 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.STM_INFO) = (yyvsp[-1].STM_INFO);
		  (yyval.STM_INFO)->stm = *((yyvsp[-7].STRING_VALUE)); delete (yyvsp[-7].STRING_VALUE);
		  (yyval.STM_INFO)->IS  = *((yyvsp[-5].RELATION)); delete (yyvsp[-5].RELATION);
		  (yyval.STM_INFO)->map = *((yyvsp[-3].MMAP)); delete (yyvsp[-3].MMAP);
		  }
#line 2407 "y.tab.c" /* yacc.c:1646  */
    break;

  case 42:
#line 590 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.STM_INFO) = new stm_info;
		  (yyval.STM_INFO)->stm = *((yyvsp[-5].STRING_VALUE)); delete (yyvsp[-5].STRING_VALUE);
		  (yyval.STM_INFO)->IS  = *((yyvsp[-3].RELATION)); delete (yyvsp[-3].RELATION);
		  (yyval.STM_INFO)->map = *((yyvsp[-1].MMAP)); delete (yyvsp[-1].MMAP);
		}
#line 2417 "y.tab.c" /* yacc.c:1646  */
    break;

  case 43:
#line 598 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.MMAP) = (yyvsp[-2].MMAP);
				  (yyval.MMAP)->partials.append(*((yyvsp[0].PMMAP))); delete (yyvsp[0].PMMAP);
				}
#line 2425 "y.tab.c" /* yacc.c:1646  */
    break;

  case 44:
#line 601 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.MMAP) = new MMap;
				  (yyval.MMAP)->partials.append(*((yyvsp[0].PMMAP))); delete (yyvsp[0].PMMAP);
				}
#line 2433 "y.tab.c" /* yacc.c:1646  */
    break;

  case 45:
#line 607 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.PMMAP) = new PartialMMap;
					  (yyval.PMMAP)->mapping = *((yyvsp[0].RELATION)); delete (yyvsp[0].RELATION);
					  (yyval.PMMAP)->bounds  = *((yyvsp[-3].RELATION)); delete (yyvsp[-3].RELATION);
					  (yyval.PMMAP)->var     = *((yyvsp[-5].STRING_VALUE)); delete (yyvsp[-5].STRING_VALUE);
					}
#line 2443 "y.tab.c" /* yacc.c:1646  */
    break;

  case 46:
#line 612 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.PMMAP) = new PartialMMap;
					  (yyval.PMMAP)->mapping = *((yyvsp[0].RELATION)); delete (yyvsp[0].RELATION);
					  (yyval.PMMAP)->bounds  = Relation::True(0);
					  (yyval.PMMAP)->var     = *((yyvsp[-2].STRING_VALUE)); delete (yyvsp[-2].STRING_VALUE);
					}
#line 2453 "y.tab.c" /* yacc.c:1646  */
    break;

  case 47:
#line 619 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.STM_INFO) = (yyvsp[-2].STM_INFO);
				  (yyval.STM_INFO)->read.append(*((yyvsp[0].READ))); delete (yyvsp[0].READ);
				}
#line 2461 "y.tab.c" /* yacc.c:1646  */
    break;

  case 48:
#line 622 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.STM_INFO) = new stm_info;
				  (yyval.STM_INFO)->read.append(*((yyvsp[0].READ))); delete (yyvsp[0].READ);
				}
#line 2469 "y.tab.c" /* yacc.c:1646  */
    break;

  case 49:
#line 627 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.READ) = (yyvsp[-1].READ); }
#line 2475 "y.tab.c" /* yacc.c:1646  */
    break;

  case 50:
#line 630 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.READ) = (yyvsp[-2].READ);
				  (yyval.READ)->partials.append(*((yyvsp[0].PREAD))); delete (yyvsp[0].PREAD);
				}
#line 2483 "y.tab.c" /* yacc.c:1646  */
    break;

  case 51:
#line 633 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.READ) = new Read;
				  (yyval.READ)->partials.append(*((yyvsp[0].PREAD))); delete (yyvsp[0].PREAD);
				}
#line 2491 "y.tab.c" /* yacc.c:1646  */
    break;

  case 52:
#line 638 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.PREAD) = new PartialRead;
				  (yyval.PREAD)->from = (yyvsp[-2].INT_VALUE);
				  (yyval.PREAD)->dataFlow = *((yyvsp[0].RELATION)); delete (yyvsp[0].RELATION);
				}
#line 2500 "y.tab.c" /* yacc.c:1646  */
    break;

  case 55:
#line 649 "../src/parser.y" /* yacc.c:1646  */
    { globalDecls->extend_both_tuples((yyvsp[-3].VAR_NAME), (yyvsp[-1].INT_VALUE)); free((yyvsp[-3].VAR_NAME)); }
#line 2506 "y.tab.c" /* yacc.c:1646  */
    break;

  case 56:
#line 651 "../src/parser.y" /* yacc.c:1646  */
    { globalDecls->extend((yyvsp[0].VAR_NAME)); free((yyvsp[0].VAR_NAME)); }
#line 2512 "y.tab.c" /* yacc.c:1646  */
    break;

  case 57:
#line 655 "../src/parser.y" /* yacc.c:1646  */
    { relationDecl = new Declaration_Site(); }
#line 2518 "y.tab.c" /* yacc.c:1646  */
    break;

  case 58:
#line 658 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = (yyvsp[-1].RELATION); 
		  if (omega_calc_debug) {
			fprintf(DebugFile,"Built relation:\n");
			(yyval.RELATION)->prefix_print(DebugFile);
			
			};
		  current_Declaration_Site = globalDecls;
		  delete relationDecl;
		}
#line 2532 "y.tab.c" /* yacc.c:1646  */
    break;

  case 59:
#line 667 "../src/parser.y" /* yacc.c:1646  */
    {
		Const_String s = (yyvsp[0].VAR_NAME);
		if (relationMap(s) == 0) {
			fprintf(stderr,"Variable %s not declared\n",(yyvsp[0].VAR_NAME));
			
			free((yyvsp[0].VAR_NAME));
			YYERROR;
			assert(0);
			};
		free((yyvsp[0].VAR_NAME));
		(yyval.RELATION) = new Relation(*relationMap(s));
		}
#line 2549 "y.tab.c" /* yacc.c:1646  */
    break;

  case 60:
#line 679 "../src/parser.y" /* yacc.c:1646  */
    {(yyval.RELATION) = (yyvsp[-1].RELATION);}
#line 2555 "y.tab.c" /* yacc.c:1646  */
    break;

  case 61:
#line 681 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = TransitiveClosure(*(yyvsp[-1].RELATION), 1,Relation::Null());
		  delete (yyvsp[-1].RELATION);
		}
#line 2564 "y.tab.c" /* yacc.c:1646  */
    break;

  case 62:
#line 686 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  int vars = (yyvsp[-1].RELATION)->n_inp();
		  *(yyval.RELATION) = Union(Identity(vars),
			      TransitiveClosure(*(yyvsp[-1].RELATION), 1,Relation::Null()));
		  delete (yyvsp[-1].RELATION);
		}
#line 2575 "y.tab.c" /* yacc.c:1646  */
    break;

  case 63:
#line 693 "../src/parser.y" /* yacc.c:1646  */
    {(yyval.RELATION) = new Relation();
                 *(yyval.RELATION)= TransitiveClosure(*(yyvsp[-3].RELATION), 1,*(yyvsp[0].RELATION));
                 delete (yyvsp[-3].RELATION);
                 delete (yyvsp[0].RELATION);
	       }
#line 2585 "y.tab.c" /* yacc.c:1646  */
    break;

  case 64:
#line 699 "../src/parser.y" /* yacc.c:1646  */
    {
		Relation o(*(yyvsp[0].RELATION));
		Relation r(*(yyvsp[0].RELATION));
		r = Join(r,LexForward((yyvsp[0].RELATION)->n_out()));
		(yyval.RELATION) = new Relation();
		*(yyval.RELATION) = Difference(o,r);
		delete (yyvsp[0].RELATION);
		}
#line 2598 "y.tab.c" /* yacc.c:1646  */
    break;

  case 65:
#line 708 "../src/parser.y" /* yacc.c:1646  */
    {
		Relation o(*(yyvsp[0].RELATION));
		Relation r(*(yyvsp[0].RELATION));
		r = Join(r,Inverse(LexForward((yyvsp[0].RELATION)->n_out())));
		(yyval.RELATION) = new Relation();
		*(yyval.RELATION) = Difference(o,r);
		delete (yyvsp[0].RELATION);
		}
#line 2611 "y.tab.c" /* yacc.c:1646  */
    break;

  case 66:
#line 717 "../src/parser.y" /* yacc.c:1646  */
    {
		Relation o(*(yyvsp[0].RELATION));
		Relation r(*(yyvsp[0].RELATION));
		r = Join(LexForward((yyvsp[0].RELATION)->n_inp()),r);
		(yyval.RELATION) = new Relation();
		*(yyval.RELATION) = Difference(o,r);
		delete (yyvsp[0].RELATION);
		}
#line 2624 "y.tab.c" /* yacc.c:1646  */
    break;

  case 67:
#line 726 "../src/parser.y" /* yacc.c:1646  */
    {
		Relation o(*(yyvsp[0].RELATION));
		Relation r(*(yyvsp[0].RELATION));
		r = Join(Inverse(LexForward((yyvsp[0].RELATION)->n_inp())),r);
		(yyval.RELATION) = new Relation();
		*(yyval.RELATION) = Difference(o,r);
		delete (yyvsp[0].RELATION);
		}
#line 2637 "y.tab.c" /* yacc.c:1646  */
    break;

  case 68:
#line 735 "../src/parser.y" /* yacc.c:1646  */
    {
		Relation c(*(yyvsp[0].RELATION));
		Relation r(*(yyvsp[0].RELATION));
		(yyval.RELATION) = new Relation(); 
		*(yyval.RELATION) = Cross_Product(Relation(*(yyvsp[0].RELATION)),c);
		delete (yyvsp[0].RELATION);
		assert((yyval.RELATION)->n_inp() ==(yyval.RELATION)->n_out());
		*(yyval.RELATION) = Difference(r,Domain(Intersection(*(yyval.RELATION),LexForward((yyval.RELATION)->n_inp()))));
		}
#line 2651 "y.tab.c" /* yacc.c:1646  */
    break;

  case 69:
#line 745 "../src/parser.y" /* yacc.c:1646  */
    {
		Relation c(*(yyvsp[0].RELATION));
		Relation r(*(yyvsp[0].RELATION));
		(yyval.RELATION) = new Relation(); 
		*(yyval.RELATION) = Cross_Product(Relation(*(yyvsp[0].RELATION)),c);
		delete (yyvsp[0].RELATION);
		assert((yyval.RELATION)->n_inp() ==(yyval.RELATION)->n_out());
		*(yyval.RELATION) = Difference(r,Range(Intersection(*(yyval.RELATION),LexForward((yyval.RELATION)->n_inp()))));
		}
#line 2665 "y.tab.c" /* yacc.c:1646  */
    break;

  case 70:
#line 755 "../src/parser.y" /* yacc.c:1646  */
    {
		(yyval.RELATION) = new Relation();
		*(yyval.RELATION) = Farkas(*(yyvsp[0].RELATION), Basic_Farkas);
		delete (yyvsp[0].RELATION);
		}
#line 2675 "y.tab.c" /* yacc.c:1646  */
    break;

  case 71:
#line 761 "../src/parser.y" /* yacc.c:1646  */
    {
		(yyval.RELATION) = new Relation();
		*(yyval.RELATION) = Farkas(*(yyvsp[0].RELATION), Decoupled_Farkas);
		delete (yyvsp[0].RELATION);
		}
#line 2685 "y.tab.c" /* yacc.c:1646  */
    break;

  case 72:
#line 767 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = ConicClosure(*(yyvsp[-1].RELATION));
		  delete (yyvsp[-1].RELATION);
		}
#line 2694 "y.tab.c" /* yacc.c:1646  */
    break;

  case 73:
#line 772 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Project_Sym(*(yyvsp[0].RELATION));
		  delete (yyvsp[0].RELATION);
		}
#line 2703 "y.tab.c" /* yacc.c:1646  */
    break;

  case 74:
#line 777 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Project_On_Sym(*(yyvsp[0].RELATION));
		  delete (yyvsp[0].RELATION);
		}
#line 2712 "y.tab.c" /* yacc.c:1646  */
    break;

  case 75:
#line 782 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Deltas(*(yyvsp[0].RELATION));
		  delete (yyvsp[0].RELATION);
		}
#line 2721 "y.tab.c" /* yacc.c:1646  */
    break;

  case 76:
#line 787 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
                  *(yyval.RELATION) = DeltasToRelation(*(yyvsp[0].RELATION),(yyvsp[0].RELATION)->n_set(),(yyvsp[0].RELATION)->n_set());
                  delete (yyvsp[0].RELATION);
                }
#line 2730 "y.tab.c" /* yacc.c:1646  */
    break;

  case 77:
#line 792 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Domain(*(yyvsp[0].RELATION));
		  delete (yyvsp[0].RELATION);
		}
#line 2739 "y.tab.c" /* yacc.c:1646  */
    break;

  case 78:
#line 797 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = VennDiagramForm(*(yyvsp[0].RELATION),Relation::True(*(yyvsp[0].RELATION)));
		  delete (yyvsp[0].RELATION);
		}
#line 2748 "y.tab.c" /* yacc.c:1646  */
    break;

  case 79:
#line 802 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = VennDiagramForm(*(yyvsp[-2].RELATION),*(yyvsp[0].RELATION));
		  delete (yyvsp[-2].RELATION);
		  delete (yyvsp[0].RELATION);
		}
#line 2758 "y.tab.c" /* yacc.c:1646  */
    break;

  case 80:
#line 808 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = ConvexHull(*(yyvsp[0].RELATION));
		  delete (yyvsp[0].RELATION);
		}
#line 2767 "y.tab.c" /* yacc.c:1646  */
    break;

  case 81:
#line 813 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Farkas(*(yyvsp[0].RELATION),Positive_Combination_Farkas);
		  delete (yyvsp[0].RELATION);
		}
#line 2776 "y.tab.c" /* yacc.c:1646  */
    break;

  case 82:
#line 818 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Farkas(*(yyvsp[0].RELATION),Convex_Combination_Farkas);
		  delete (yyvsp[0].RELATION);
		}
#line 2785 "y.tab.c" /* yacc.c:1646  */
    break;

  case 83:
#line 823 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = CheckForConvexRepresentation(CheckForConvexPairs(*(yyvsp[0].RELATION)));
		  delete (yyvsp[0].RELATION);
		}
#line 2794 "y.tab.c" /* yacc.c:1646  */
    break;

  case 84:
#line 828 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = CheckForConvexRepresentation(*(yyvsp[0].RELATION));
		  delete (yyvsp[0].RELATION);
		}
#line 2803 "y.tab.c" /* yacc.c:1646  */
    break;

  case 85:
#line 833 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = AffineHull(*(yyvsp[0].RELATION));
		  delete (yyvsp[0].RELATION);
		}
#line 2812 "y.tab.c" /* yacc.c:1646  */
    break;

  case 86:
#line 838 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = ConicHull(*(yyvsp[0].RELATION));
		  delete (yyvsp[0].RELATION);
		}
#line 2821 "y.tab.c" /* yacc.c:1646  */
    break;

  case 87:
#line 843 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = LinearHull(*(yyvsp[0].RELATION));
		  delete (yyvsp[0].RELATION);
		}
#line 2830 "y.tab.c" /* yacc.c:1646  */
    break;

  case 88:
#line 848 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Hull(*(yyvsp[0].RELATION),false,1,Null_Relation());
		  delete (yyvsp[0].RELATION);
		}
#line 2839 "y.tab.c" /* yacc.c:1646  */
    break;

  case 89:
#line 853 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Hull(*(yyvsp[-2].RELATION),false,1,*(yyvsp[0].RELATION));
		  delete (yyvsp[-2].RELATION);
		  delete (yyvsp[0].RELATION);
		}
#line 2849 "y.tab.c" /* yacc.c:1646  */
    break;

  case 90:
#line 859 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Approximate(*(yyvsp[0].RELATION));
		  delete (yyvsp[0].RELATION);
		}
#line 2858 "y.tab.c" /* yacc.c:1646  */
    break;

  case 91:
#line 864 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Range(*(yyvsp[0].RELATION));
		  delete (yyvsp[0].RELATION);
		}
#line 2867 "y.tab.c" /* yacc.c:1646  */
    break;

  case 92:
#line 869 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Inverse(*(yyvsp[0].RELATION));
		  delete (yyvsp[0].RELATION);
		}
#line 2876 "y.tab.c" /* yacc.c:1646  */
    break;

  case 93:
#line 874 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Complement(*(yyvsp[0].RELATION));
		  delete (yyvsp[0].RELATION);
		}
#line 2885 "y.tab.c" /* yacc.c:1646  */
    break;

  case 94:
#line 879 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Gist(*(yyvsp[-2].RELATION),*(yyvsp[0].RELATION),1);
		  delete (yyvsp[-2].RELATION);
		  delete (yyvsp[0].RELATION);
		}
#line 2895 "y.tab.c" /* yacc.c:1646  */
    break;

  case 95:
#line 885 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Composition(*(yyvsp[-3].RELATION),*(yyvsp[-1].RELATION));
		  delete (yyvsp[-3].RELATION);
		  delete (yyvsp[-1].RELATION);
		}
#line 2905 "y.tab.c" /* yacc.c:1646  */
    break;

  case 96:
#line 891 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Composition(*(yyvsp[-2].RELATION),*(yyvsp[0].RELATION));
		  delete (yyvsp[-2].RELATION);
		  delete (yyvsp[0].RELATION);
		}
#line 2915 "y.tab.c" /* yacc.c:1646  */
    break;

  case 97:
#line 897 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = After(*(yyvsp[-2].RELATION),(yyvsp[0].INT_VALUE),(yyvsp[0].INT_VALUE));
		  delete (yyvsp[-2].RELATION);
		  (*(yyval.RELATION)).prefix_print(stdout);
		}
#line 2925 "y.tab.c" /* yacc.c:1646  */
    break;

  case 98:
#line 903 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Composition(*(yyvsp[0].RELATION),*(yyvsp[-2].RELATION));
		  delete (yyvsp[-2].RELATION);
		  delete (yyvsp[0].RELATION);
		}
#line 2935 "y.tab.c" /* yacc.c:1646  */
    break;

  case 99:
#line 909 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Restrict_Range(*(yyvsp[-2].RELATION),*(yyvsp[0].RELATION));
		  delete (yyvsp[-2].RELATION);
		  delete (yyvsp[0].RELATION);
		}
#line 2945 "y.tab.c" /* yacc.c:1646  */
    break;

  case 100:
#line 915 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Restrict_Domain(*(yyvsp[-2].RELATION),*(yyvsp[0].RELATION));
		  delete (yyvsp[-2].RELATION);
		  delete (yyvsp[0].RELATION);
		}
#line 2955 "y.tab.c" /* yacc.c:1646  */
    break;

  case 101:
#line 921 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Intersection(*(yyvsp[-2].RELATION),*(yyvsp[0].RELATION));
		  delete (yyvsp[-2].RELATION);
		  delete (yyvsp[0].RELATION);
		}
#line 2965 "y.tab.c" /* yacc.c:1646  */
    break;

  case 102:
#line 927 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
                  *(yyval.RELATION) = Difference(*(yyvsp[-2].RELATION),*(yyvsp[0].RELATION));
                  delete (yyvsp[-2].RELATION);
                  delete (yyvsp[0].RELATION);
                }
#line 2975 "y.tab.c" /* yacc.c:1646  */
    break;

  case 103:
#line 933 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Union(*(yyvsp[-2].RELATION),*(yyvsp[0].RELATION));
		  delete (yyvsp[-2].RELATION);
		  delete (yyvsp[0].RELATION);
		}
#line 2985 "y.tab.c" /* yacc.c:1646  */
    break;

  case 104:
#line 939 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
		  *(yyval.RELATION) = Cross_Product(*(yyvsp[-2].RELATION),*(yyvsp[0].RELATION));
		  delete (yyvsp[-2].RELATION);
		  delete (yyvsp[0].RELATION);
		}
#line 2995 "y.tab.c" /* yacc.c:1646  */
    break;

  case 105:
#line 945 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
                  *(yyval.RELATION) = Union(*(yyvsp[0].RELATION), Relation::Unknown(*(yyvsp[0].RELATION)));
                  delete (yyvsp[0].RELATION);
                }
#line 3004 "y.tab.c" /* yacc.c:1646  */
    break;

  case 106:
#line 950 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
                  *(yyval.RELATION) = Intersection(*(yyvsp[0].RELATION), Relation::Unknown(*(yyvsp[0].RELATION)));
                  delete (yyvsp[0].RELATION);
                }
#line 3013 "y.tab.c" /* yacc.c:1646  */
    break;

  case 107:
#line 955 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
                  *(yyval.RELATION) = Upper_Bound(*(yyvsp[0].RELATION));
                  delete (yyvsp[0].RELATION);
                }
#line 3022 "y.tab.c" /* yacc.c:1646  */
    break;

  case 108:
#line 960 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
                  *(yyval.RELATION) = Lower_Bound(*(yyvsp[0].RELATION));
                  delete (yyvsp[0].RELATION);
                }
#line 3031 "y.tab.c" /* yacc.c:1646  */
    break;

  case 109:
#line 965 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
                  *(yyval.RELATION) = Sample_Solution(*(yyvsp[0].RELATION));
                  delete (yyvsp[0].RELATION);
                }
#line 3040 "y.tab.c" /* yacc.c:1646  */
    break;

  case 110:
#line 970 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = new Relation();
                  *(yyval.RELATION) = Symbolic_Solution(*(yyvsp[0].RELATION));
                  delete (yyvsp[0].RELATION);
                }
#line 3049 "y.tab.c" /* yacc.c:1646  */
    break;

  case 111:
#line 974 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.RELATION) = (yyvsp[0].RELATION); }
#line 3055 "y.tab.c" /* yacc.c:1646  */
    break;

  case 112:
#line 976 "../src/parser.y" /* yacc.c:1646  */
    {
		  if (((yyvsp[0].RELATION))->is_satisfiable())
			  {
			    fprintf(stderr,"assert_unsatisfiable failed on ");
			    ((yyvsp[0].RELATION))->print_with_subs(stderr);
			    Exit(1);
			  }
		  (yyval.RELATION)=(yyvsp[0].RELATION);
		}
#line 3069 "y.tab.c" /* yacc.c:1646  */
    break;

  case 113:
#line 989 "../src/parser.y" /* yacc.c:1646  */
    {currentTuple = Output_Tuple;}
#line 3075 "y.tab.c" /* yacc.c:1646  */
    break;

  case 114:
#line 990 "../src/parser.y" /* yacc.c:1646  */
    {currentTuple = Input_Tuple;}
#line 3081 "y.tab.c" /* yacc.c:1646  */
    break;

  case 115:
#line 990 "../src/parser.y" /* yacc.c:1646  */
    {
		Relation * r = new Relation((yyvsp[-5].TUPLE_DESCRIPTOR)->size,(yyvsp[-2].TUPLE_DESCRIPTOR)->size);
		resetGlobals();
		F_And *f = r->add_and();
		int i;
		for(i=1;i<=(yyvsp[-5].TUPLE_DESCRIPTOR)->size;i++) {	
			(yyvsp[-5].TUPLE_DESCRIPTOR)->vars[i]->vid = r->input_var(i);
			if (!(yyvsp[-5].TUPLE_DESCRIPTOR)->vars[i]->anonymous) 
				r->name_input_var(i,(yyvsp[-5].TUPLE_DESCRIPTOR)->vars[i]->stripped_name);
			};
		for(i=1;i<=(yyvsp[-2].TUPLE_DESCRIPTOR)->size;i++) {
			(yyvsp[-2].TUPLE_DESCRIPTOR)->vars[i]->vid = r->output_var(i);
			if (!(yyvsp[-2].TUPLE_DESCRIPTOR)->vars[i]->anonymous) 
				r->name_output_var(i,(yyvsp[-2].TUPLE_DESCRIPTOR)->vars[i]->stripped_name);
			};
		foreach(e,Exp*,(yyvsp[-5].TUPLE_DESCRIPTOR)->eq_constraints, install_eq(f,e,0));
                foreach(e,Exp*,(yyvsp[-5].TUPLE_DESCRIPTOR)->geq_constraints, install_geq(f,e,0)); 
		foreach(c,strideConstraint*,(yyvsp[-5].TUPLE_DESCRIPTOR)->stride_constraints, install_stride(f,c));
		foreach(e,Exp*,(yyvsp[-2].TUPLE_DESCRIPTOR)->eq_constraints, install_eq(f,e,0));
		foreach(e,Exp*,(yyvsp[-2].TUPLE_DESCRIPTOR)->geq_constraints, install_geq(f,e,0));
		foreach(c,strideConstraint*,(yyvsp[-2].TUPLE_DESCRIPTOR)->stride_constraints, install_stride(f,c));
		if ((yyvsp[0].ASTP)) (yyvsp[0].ASTP)->install(f);
		delete (yyvsp[-5].TUPLE_DESCRIPTOR);
		delete (yyvsp[-2].TUPLE_DESCRIPTOR);
		delete (yyvsp[0].ASTP);
		(yyval.RELATION) = r; }
#line 3112 "y.tab.c" /* yacc.c:1646  */
    break;

  case 116:
#line 1016 "../src/parser.y" /* yacc.c:1646  */
    {
	        Relation * r = new Relation((yyvsp[-1].TUPLE_DESCRIPTOR)->size);
		resetGlobals();
		F_And *f = r->add_and();
		int i;
		for(i=1;i<=(yyvsp[-1].TUPLE_DESCRIPTOR)->size;i++) {	
			(yyvsp[-1].TUPLE_DESCRIPTOR)->vars[i]->vid = r->set_var(i);
			if (!(yyvsp[-1].TUPLE_DESCRIPTOR)->vars[i]->anonymous) 
				r->name_set_var(i,(yyvsp[-1].TUPLE_DESCRIPTOR)->vars[i]->stripped_name);
			};
                foreach(e,Exp*,(yyvsp[-1].TUPLE_DESCRIPTOR)->eq_constraints, install_eq(f,e,0)); 
		foreach(e,Exp*,(yyvsp[-1].TUPLE_DESCRIPTOR)->geq_constraints, install_geq(f,e,0));
		foreach(c,strideConstraint*,(yyvsp[-1].TUPLE_DESCRIPTOR)->stride_constraints, install_stride(f,c));
		if ((yyvsp[0].ASTP)) (yyvsp[0].ASTP)->install(f);
		delete (yyvsp[-1].TUPLE_DESCRIPTOR);
		delete (yyvsp[0].ASTP);
		(yyval.RELATION) = r; }
#line 3134 "y.tab.c" /* yacc.c:1646  */
    break;

  case 117:
#line 1033 "../src/parser.y" /* yacc.c:1646  */
    {
		Relation * r = new Relation(0,0);
		F_And *f = r->add_and();
		(yyvsp[0].ASTP)->install(f);
		delete (yyvsp[0].ASTP);
		(yyval.RELATION) = r;
		}
#line 3146 "y.tab.c" /* yacc.c:1646  */
    break;

  case 118:
#line 1042 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.ASTP) = (yyvsp[0].ASTP); }
#line 3152 "y.tab.c" /* yacc.c:1646  */
    break;

  case 119:
#line 1043 "../src/parser.y" /* yacc.c:1646  */
    {(yyval.ASTP) = 0;}
#line 3158 "y.tab.c" /* yacc.c:1646  */
    break;

  case 123:
#line 1052 "../src/parser.y" /* yacc.c:1646  */
    { currentTupleDescriptor = new tupleDescriptor; tuplePos = 1; }
#line 3164 "y.tab.c" /* yacc.c:1646  */
    break;

  case 124:
#line 1054 "../src/parser.y" /* yacc.c:1646  */
    {(yyval.TUPLE_DESCRIPTOR) = currentTupleDescriptor; }
#line 3170 "y.tab.c" /* yacc.c:1646  */
    break;

  case 128:
#line 1064 "../src/parser.y" /* yacc.c:1646  */
    { Declaration_Site *ds = defined((yyvsp[0].VAR_NAME));
	  if (!ds) currentTupleDescriptor->extend((yyvsp[0].VAR_NAME),currentTuple,tuplePos);
	  else {
	      Variable_Ref * v = lookupScalar((yyvsp[0].VAR_NAME));
	      assert(v);
	      if (ds != globalDecls) 
		currentTupleDescriptor->extend((yyvsp[0].VAR_NAME), new Exp(v));
	      else 
		currentTupleDescriptor->extend(new Exp(v));
	      }
	  free((yyvsp[0].VAR_NAME));
	  tuplePos++;
	}
#line 3188 "y.tab.c" /* yacc.c:1646  */
    break;

  case 129:
#line 1078 "../src/parser.y" /* yacc.c:1646  */
    {currentTupleDescriptor->extend(); tuplePos++; }
#line 3194 "y.tab.c" /* yacc.c:1646  */
    break;

  case 130:
#line 1080 "../src/parser.y" /* yacc.c:1646  */
    {currentTupleDescriptor->extend((yyvsp[0].EXP)); tuplePos++; }
#line 3200 "y.tab.c" /* yacc.c:1646  */
    break;

  case 131:
#line 1082 "../src/parser.y" /* yacc.c:1646  */
    {currentTupleDescriptor->extend((yyvsp[-2].EXP),(yyvsp[0].EXP)); tuplePos++; }
#line 3206 "y.tab.c" /* yacc.c:1646  */
    break;

  case 132:
#line 1084 "../src/parser.y" /* yacc.c:1646  */
    {currentTupleDescriptor->extend((yyvsp[-4].EXP),(yyvsp[-2].EXP),(yyvsp[0].INT_VALUE)); tuplePos++; }
#line 3212 "y.tab.c" /* yacc.c:1646  */
    break;

  case 133:
#line 1088 "../src/parser.y" /* yacc.c:1646  */
    {(yyval.VAR_LIST) = (yyvsp[-2].VAR_LIST); (yyval.VAR_LIST)->insert((yyvsp[0].VAR_NAME)); }
#line 3218 "y.tab.c" /* yacc.c:1646  */
    break;

  case 134:
#line 1089 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.VAR_LIST) = new VarList;
		(yyval.VAR_LIST)->insert((yyvsp[0].VAR_NAME)); }
#line 3225 "y.tab.c" /* yacc.c:1646  */
    break;

  case 135:
#line 1094 "../src/parser.y" /* yacc.c:1646  */
    {
		(yyval.DECLARATION_SITE) = current_Declaration_Site = new Declaration_Site((yyvsp[0].VAR_LIST));
		foreach(s,char *, *(yyvsp[0].VAR_LIST), delete s);
		delete (yyvsp[0].VAR_LIST);
		}
#line 3235 "y.tab.c" /* yacc.c:1646  */
    break;

  case 136:
#line 1103 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.DECLARATION_SITE) = (yyvsp[0].DECLARATION_SITE); }
#line 3241 "y.tab.c" /* yacc.c:1646  */
    break;

  case 137:
#line 1104 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.DECLARATION_SITE) = (yyvsp[-1].DECLARATION_SITE); }
#line 3247 "y.tab.c" /* yacc.c:1646  */
    break;

  case 138:
#line 1107 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.ASTP) = new AST_And((yyvsp[-2].ASTP),(yyvsp[0].ASTP)); }
#line 3253 "y.tab.c" /* yacc.c:1646  */
    break;

  case 139:
#line 1108 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.ASTP) = new AST_Or((yyvsp[-2].ASTP),(yyvsp[0].ASTP)); }
#line 3259 "y.tab.c" /* yacc.c:1646  */
    break;

  case 140:
#line 1109 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.ASTP) = (yyvsp[0].ASTCP); }
#line 3265 "y.tab.c" /* yacc.c:1646  */
    break;

  case 141:
#line 1110 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.ASTP) = (yyvsp[-1].ASTP); }
#line 3271 "y.tab.c" /* yacc.c:1646  */
    break;

  case 142:
#line 1111 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.ASTP) = new AST_Not((yyvsp[0].ASTP)); }
#line 3277 "y.tab.c" /* yacc.c:1646  */
    break;

  case 143:
#line 1113 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.ASTP) = new AST_exists((yyvsp[-3].DECLARATION_SITE),(yyvsp[-1].ASTP)); }
#line 3283 "y.tab.c" /* yacc.c:1646  */
    break;

  case 144:
#line 1115 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.ASTP) = new AST_forall((yyvsp[-3].DECLARATION_SITE),(yyvsp[-1].ASTP)); }
#line 3289 "y.tab.c" /* yacc.c:1646  */
    break;

  case 153:
#line 1135 "../src/parser.y" /* yacc.c:1646  */
    { popScope(); }
#line 3295 "y.tab.c" /* yacc.c:1646  */
    break;

  case 154:
#line 1139 "../src/parser.y" /* yacc.c:1646  */
    {
		(yyval.EXP_LIST) = (yyvsp[0].EXP_LIST); 
		(yyval.EXP_LIST)->insert((yyvsp[-2].EXP));
		}
#line 3304 "y.tab.c" /* yacc.c:1646  */
    break;

  case 155:
#line 1143 "../src/parser.y" /* yacc.c:1646  */
    {
		(yyval.EXP_LIST) = new ExpList;
		(yyval.EXP_LIST)->insert((yyvsp[0].EXP));
		}
#line 3313 "y.tab.c" /* yacc.c:1646  */
    break;

  case 156:
#line 1150 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.ASTCP) = new AST_constraints((yyvsp[-2].EXP_LIST),(yyvsp[-1].REL_OPERATOR),(yyvsp[0].EXP_LIST)); }
#line 3319 "y.tab.c" /* yacc.c:1646  */
    break;

  case 157:
#line 1152 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.ASTCP) = new AST_constraints((yyvsp[-2].EXP_LIST),(yyvsp[-1].REL_OPERATOR),(yyvsp[0].ASTCP)); }
#line 3325 "y.tab.c" /* yacc.c:1646  */
    break;

  case 158:
#line 1157 "../src/parser.y" /* yacc.c:1646  */
    { Variable_Ref * v = lookupScalar((yyvsp[0].VAR_NAME));
		  if (!v) YYERROR;
		  (yyval.EXP) = new Exp(v); 
		  free((yyvsp[0].VAR_NAME)); 
		  }
#line 3335 "y.tab.c" /* yacc.c:1646  */
    break;

  case 159:
#line 1162 "../src/parser.y" /* yacc.c:1646  */
    {argCount = 1;}
#line 3341 "y.tab.c" /* yacc.c:1646  */
    break;

  case 160:
#line 1163 "../src/parser.y" /* yacc.c:1646  */
    {Variable_Ref *v;
		 if ((yyvsp[-1].ARGUMENT_TUPLE) == Input_Tuple) v = functionOfInput[(yyvsp[-4].VAR_NAME)];
		 else v = functionOfOutput[(yyvsp[-4].VAR_NAME)];
		 if (v == 0) {
			fprintf(stderr,"Function %s(...) not declared\n",(yyvsp[-4].VAR_NAME));
			free((yyvsp[-4].VAR_NAME));
			YYERROR;
			}
		 free((yyvsp[-4].VAR_NAME));
		 (yyval.EXP) = new Exp(v);
		}
#line 3357 "y.tab.c" /* yacc.c:1646  */
    break;

  case 161:
#line 1174 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.EXP) = (yyvsp[-1].EXP);}
#line 3363 "y.tab.c" /* yacc.c:1646  */
    break;

  case 162:
#line 1180 "../src/parser.y" /* yacc.c:1646  */
    {
		Variable_Ref * v = lookupScalar((yyvsp[0].VAR_NAME));
		if (!v) YYERROR;
		 free((yyvsp[0].VAR_NAME));
		 if (v->pos != argCount || v->of != (yyvsp[-2].ARGUMENT_TUPLE) || v->of != Input_Tuple && v->of != Output_Tuple) {
			fprintf(stderr,"arguments to function must be prefix of input or output tuple\n");
			
			YYERROR;
			}
		 (yyval.ARGUMENT_TUPLE) = v->of;
		 argCount++;
		}
#line 3380 "y.tab.c" /* yacc.c:1646  */
    break;

  case 163:
#line 1192 "../src/parser.y" /* yacc.c:1646  */
    { Variable_Ref * v = lookupScalar((yyvsp[0].VAR_NAME));
		if (!v) YYERROR;
		 free((yyvsp[0].VAR_NAME));
		 if (v->pos != argCount || v->of != Input_Tuple && v->of != Output_Tuple) {
			fprintf(stderr,"arguments to function must be prefix of input or output tuple\n");
			
			YYERROR;
			}
		 (yyval.ARGUMENT_TUPLE) = v->of;
		 argCount++;
		}
#line 3396 "y.tab.c" /* yacc.c:1646  */
    break;

  case 164:
#line 1205 "../src/parser.y" /* yacc.c:1646  */
    {(yyval.EXP) = new Exp((yyvsp[0].INT_VALUE));}
#line 3402 "y.tab.c" /* yacc.c:1646  */
    break;

  case 165:
#line 1206 "../src/parser.y" /* yacc.c:1646  */
    {(yyval.EXP) = multiply((yyvsp[-1].INT_VALUE),(yyvsp[0].EXP));}
#line 3408 "y.tab.c" /* yacc.c:1646  */
    break;

  case 166:
#line 1207 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.EXP) = (yyvsp[0].EXP); }
#line 3414 "y.tab.c" /* yacc.c:1646  */
    break;

  case 167:
#line 1208 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.EXP) = ::negate((yyvsp[0].EXP));}
#line 3420 "y.tab.c" /* yacc.c:1646  */
    break;

  case 168:
#line 1209 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.EXP) = add((yyvsp[-2].EXP),(yyvsp[0].EXP));}
#line 3426 "y.tab.c" /* yacc.c:1646  */
    break;

  case 169:
#line 1210 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.EXP) = subtract((yyvsp[-2].EXP),(yyvsp[0].EXP));}
#line 3432 "y.tab.c" /* yacc.c:1646  */
    break;

  case 170:
#line 1211 "../src/parser.y" /* yacc.c:1646  */
    { (yyval.EXP) = multiply((yyvsp[-2].EXP),(yyvsp[0].EXP));}
#line 3438 "y.tab.c" /* yacc.c:1646  */
    break;

  case 171:
#line 1217 "../src/parser.y" /* yacc.c:1646  */
    {
		  Dynamic_Array1<Relation> *final =
		    Reachable_Nodes(reachable_info);
		  (yyval.RELATION_ARRAY_1D) = final;
		}
#line 3448 "y.tab.c" /* yacc.c:1646  */
    break;

  case 172:
#line 1226 "../src/parser.y" /* yacc.c:1646  */
    {
		  Dynamic_Array1<Relation> *final =
		    Reachable_Nodes(reachable_info);
		  int index = reachable_info->node_names.index(String((yyvsp[-3].VAR_NAME)));
		  assert(index != 0 && "No such node");
		  (yyval.RELATION) = new Relation; 
		  *(yyval.RELATION) = (*final)[index];
		  delete final;
		  delete reachable_info;
		  delete (yyvsp[-3].VAR_NAME);
		}
#line 3464 "y.tab.c" /* yacc.c:1646  */
    break;

  case 173:
#line 1241 "../src/parser.y" /* yacc.c:1646  */
    { int sz = reachable_info->node_names.size();
		reachable_info->node_arity.reallocate(sz);
	  	reachable_info->transitions.resize(sz+1,sz+1);
	  	reachable_info->start_nodes.resize(sz+1);
	      }
#line 3474 "y.tab.c" /* yacc.c:1646  */
    break;

  case 174:
#line 1249 "../src/parser.y" /* yacc.c:1646  */
    { reachable_info->node_names.append(String((yyvsp[0].VAR_NAME)));
		delete (yyvsp[0].VAR_NAME); }
#line 3481 "y.tab.c" /* yacc.c:1646  */
    break;

  case 175:
#line 1251 "../src/parser.y" /* yacc.c:1646  */
    { reachable_info = new reachable_information;
		reachable_info->node_names.append(String((yyvsp[0].VAR_NAME)));
		delete (yyvsp[0].VAR_NAME); }
#line 3489 "y.tab.c" /* yacc.c:1646  */
    break;

  case 176:
#line 1258 "../src/parser.y" /* yacc.c:1646  */
    {  
	   int i,j;
	   int n_nodes = reachable_info->node_names.size();
	   Tuple<int> &arity = reachable_info->node_arity;
	   Dynamic_Array2<Relation> &transitions = reachable_info->transitions;

           /* fixup unspecified transitions to be false */
	   /* find arity */
	   for(i = 1; i <= n_nodes; i++) arity[i] = -1;
	   for(i = 1; i <= n_nodes; i++)
	     for(j = 1; j <= n_nodes; j++)
		if(! transitions[i][j].is_null()) {
		  int in_arity = transitions[i][j].n_inp();
		  int out_arity = transitions[i][j].n_out();
		  if(arity[i] < 0) arity[i] = in_arity;
		  if(arity[j] < 0) arity[j] = out_arity;
		  if(in_arity != arity[i] || out_arity != arity[j]) {
		    fprintf(stderr,
			    "Arity mismatch in node transition: %s -> %s",
			    (const char *) reachable_info->node_names[i],
			    (const char *) reachable_info->node_names[j]);
				
			assert(0);
		    YYERROR;
		  }
		}
	   for(i = 1; i <= n_nodes; i++) 
	     if(arity[i] < 0) arity[i] = 0;
	   /* Fill in false relations */
	   for(i = 1; i <= n_nodes; i++)
	     for(j = 1; j <= n_nodes; j++)
		if(transitions[i][j].is_null())
		  transitions[i][j] = Relation::False(arity[i],arity[j]);


          /* fixup unused start node positions */
	   Dynamic_Array1<Relation> &nodes = reachable_info->start_nodes;
	   for(i = 1; i <= n_nodes; i++) 
	     if(nodes[i].is_null()) 
		nodes[i] = Relation::False(arity[i]);
	     else
		if(nodes[i].n_set() != arity[i]){
		    fprintf(stderr,"Arity mismatch in start node %s",
			    (const char *) reachable_info->node_names[i]);
				
		assert(0);
		    YYERROR;
		}
 	}
#line 3543 "y.tab.c" /* yacc.c:1646  */
    break;

  case 177:
#line 1311 "../src/parser.y" /* yacc.c:1646  */
    {  int n_nodes = reachable_info->node_names.size();
	     int index = reachable_info->node_names.index((yyvsp[-2].VAR_NAME));
	     assert(index != 0 && index <= n_nodes);
	     reachable_info->start_nodes[index] = *(yyvsp[0].RELATION);
	     delete (yyvsp[-2].VAR_NAME);
	     delete (yyvsp[0].RELATION);
	  }
#line 3555 "y.tab.c" /* yacc.c:1646  */
    break;

  case 178:
#line 1319 "../src/parser.y" /* yacc.c:1646  */
    {  int n_nodes = reachable_info->node_names.size();
	     int from_index = reachable_info->node_names.index((yyvsp[-4].VAR_NAME));
	     int   to_index = reachable_info->node_names.index((yyvsp[-2].VAR_NAME));
	     assert(from_index != 0 && to_index != 0);
	     assert(from_index <= n_nodes && to_index <= n_nodes);
	     reachable_info->transitions[from_index][to_index] = *(yyvsp[0].RELATION);
	     delete (yyvsp[-4].VAR_NAME);
	     delete (yyvsp[-2].VAR_NAME);
	     delete (yyvsp[0].RELATION);
	  }
#line 3570 "y.tab.c" /* yacc.c:1646  */
    break;

  case 179:
#line 1330 "../src/parser.y" /* yacc.c:1646  */
    {  int n_nodes = reachable_info->node_names.size();
	     int from_index = reachable_info->node_names.index((yyvsp[-4].VAR_NAME));
	     int   to_index = reachable_info->node_names.index((yyvsp[-2].VAR_NAME));
	     assert(from_index != 0 && to_index != 0);
	     assert(from_index <= n_nodes && to_index <= n_nodes);
	     reachable_info->transitions[from_index][to_index] = *(yyvsp[0].RELATION);
	     delete (yyvsp[-4].VAR_NAME);
	     delete (yyvsp[-2].VAR_NAME);
	     delete (yyvsp[0].RELATION);
	  }
#line 3585 "y.tab.c" /* yacc.c:1646  */
    break;

  case 180:
#line 1341 "../src/parser.y" /* yacc.c:1646  */
    {  int n_nodes = reachable_info->node_names.size();
	     int index = reachable_info->node_names.index((yyvsp[-2].VAR_NAME));
	     assert(index != 0 && index <= n_nodes);
	     reachable_info->start_nodes[index] = *(yyvsp[0].RELATION);
	     delete (yyvsp[-2].VAR_NAME);
	     delete (yyvsp[0].RELATION);
	  }
#line 3597 "y.tab.c" /* yacc.c:1646  */
    break;


#line 3601 "y.tab.c" /* yacc.c:1646  */
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
      yyerror (YY_("syntax error"));
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
        yyerror (yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }



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
                      yytoken, &yylval);
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


      yydestruct ("Error: popping",
                  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


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
  yyerror (YY_("memory exhausted"));
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
                  yytoken, &yylval);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
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
  return yyresult;
}
#line 1350 "../src/parser.y" /* yacc.c:1906  */


extern FILE *yyin;


#if ! defined(OMIT_GETRUSAGE)
#ifdef __sparc__
extern "C" int getrusage (int, struct rusage*);
#endif


namespace omega {

#if !defined(OMIT_GETRUSAGE)
#include <sys/types.h>
#include <sys/time.h>
#include <sys/resource.h>

struct rusage start_time;
#endif

#if defined BRAIN_DAMAGED_FREE
void free(void *p)
    {
    free((char *)p);
    }

void *realloc(void *p, size_t s)
    {
    return realloc((malloc_t) p, s);
    }
#endif

void start_clock( void )
    {
    getrusage(RUSAGE_SELF, &start_time);
    }

int clock_diff( void )
    {
    struct rusage current_time;
    getrusage(RUSAGE_SELF, &current_time);
    return (current_time.ru_utime.tv_sec -start_time.ru_utime.tv_sec)*1000000 +
           (current_time.ru_utime.tv_usec-start_time.ru_utime.tv_usec);
    }
#endif

void printUsage(FILE *outf, char **argv) {
    fprintf(outf, "usage: %s {-R} {-D[facility][level]...} infile\n  -R means skip redundant conjunct elimination\n  -D sets debugging level as follows:\n    a = all debugging flags\n    g = code generation\n    l = calculator\n    c = omega core\n    p = presburger functions\n    r = relational operators\n    t = transitive closure\nAll debugging output goes to %s\n",argv[0],DEBUG_FILE_NAME);
}

int omega_calc_debug;
int omega_echo_input;

} // end namespace omega
//size of (parser.l ==> scanBuf)
#define INTERACTIVE_MAX_BUFF_SIZE 1024
int main(int argc, char **argv){
  redundant_conj_level = 2;
  current_Declaration_Site = globalDecls = new Global_Declaration_Site();
#if YYDEBUG != 0
  yydebug  = 1;
#endif
  int i;
  char * fileName = 0;
  //for test
  char buffer[YY_BUF_SIZE];
  
  printf("# %s (based on %s, %s):\n",CALC_VERSION_STRING, Omega_Library_Version, Omega_Library_Date);
  //Modified by locle for supporting incrementally calling
  fflush(stdout);
  calc_all_debugging_off();

#ifdef SPEED
  DebugFile = fopen("/dev/null","w");
  assert(DebugFile);
#else
  DebugFile = fopen(DEBUG_FILE_NAME, "w");
  if (!DebugFile) {
    fprintf(stderr, "Can't open debug file %s\n", DEBUG_FILE_NAME);
	
    DebugFile = stderr;
  }
  setbuf(DebugFile,0);
#endif

  closure_presburger_debug = 0;
  //default not echo the input- by locle
  omega_echo_input = 0;

  setOutputFile(DebugFile);

  // Process flags
  for(i=1; i<argc; i++) {
    if(argv[i][0] == '-') {
      int j = 1, c;
      while((c=argv[i][j++]) != 0) {
	switch(c) {
	case 'D':
	    if (! process_calc_debugging_flags(argv[i],j)) {
		printUsage(stderr,argv);
		Exit(1);
	    }
	    break;
	case 'G':
	    { 
	      fprintf(stderr,"Note: specifying number of GEQ's is no longer useful.\n");
	      while(argv[i][j] != 0) j++;
	    }
	    break;
	case 'E':
	    {
	      fprintf(stderr,"Note: specifying number of EQ's is no longer useful.\n");
	      while(argv[i][j] != 0) j++;
	    }
	    break;
	case 'R':
	    redundant_conj_level = 1;
	    break;
    case 'I': //by locle
     // omega_echo_input = 1;
       break;
      // Other future options go here
	default:
	  fprintf(stderr, "\nUnknown flag -%c\n", c);
	  printUsage(stderr,argv);
	  Exit(1);
	}
      }
    } 
   else {
     // Make sure this is a file name
     if (fileName) {
	fprintf(stderr,"\nCan only handle a single input file\n");
	printUsage(stderr,argv);
	Exit(1);
	};
     fileName = argv[i];
	 
     yyin = fopen(fileName, "r");
     if (!yyin) {
	    fprintf(stderr, "\nCan't open input file %s\n",fileName);
	    printUsage(stderr,argv);
	    Exit(1);
	    };
     }
   }
  //Modified by locle for supporting incrementally calling	
  initializeOmega();
  // for debugging
  /* FILE * flog = fopen("oc_temp_locle", "a+"); */
  // END for debugging
    if (fileName)
  {
    // for debugging
    /* int a=0; */
    /* printf("#xxxx0\n");fprintf(flog, "%d", a); */
    /* fflush(flog); */
    /* fclose(flog); */
    // END for debugging
    initializeScanBuffer();
    yyparse();
    /* printf("#xxxx2\n"); */
  }
  else
  {
    // for debugging
    /* int b=1; */
    /* int c = 2; */
    /* int e = 3; */
    /* printf("#xxxx1\n");fprintf(flog, "%d", b); */
    /* fflush(flog); */
    /* fclose(flog); */
     // END for debugging

     yyin = NULL;
	//FILE *fwriter;
	//fwriter = fopen(".test", "w");

    while(true){
      // for debugging
      /* flog = fopen("oc_temp_locle", "a+"); */
      /* printf("#xxxx3\n");fprintf(flog, "%d", c); */
      /* fflush(flog); */
      /* fclose(flog); */
      // END for debugging
      initializeScanBuffer();
      memset(buffer, 0, YY_BUF_SIZE);

      //get input stream byte by byte
	  int c = '*';
	  yy_size_t n;
      int is_first_round = 1;
      FILE *fwriter;
      //fwriter = fopen(".oc_temp_hip", "w");
      //yy_size_t count = 0;
      for ( n = 0; n < YY_BUF_SIZE && (c = getc( stdin )) != EOF && c != ';'; ++n ){
        /*
         if (c == '\n') count = 0;
         count++;
        //insert newline to prevent overflow
        if (count > INTERACTIVE_MAX_BUFF_SIZE - 32)
        {
          if (c == ' ' || c == ')' || c == '(' || c == '+' || c == '&' || c == ',') {
            buffer[n] = (char) c;
            n++;
            c = '\n';
            count = 0;
          }
          }*/
        if (c != ' ')
          buffer[n] = (char) c;
        else
          n--;
        //no more space
        if (n == YY_BUF_SIZE-2){
          if (is_first_round == 1){
            is_first_round = 0;
            //we need an empty file
            fwriter = fopen(".oc_temp_hip", "w+");
            //fprintf(fwriter, "%s", buffer);
            fwrite(buffer, (n+1), sizeof(char), fwriter);
            fflush(fwriter);
            fclose(fwriter);
          }
          else {
            fwriter = fopen(".oc_temp_hip", "a");
            //fprintf(fwriter, "%s", buffer);
            fwrite(buffer, (n+1), sizeof(char), fwriter);
            fflush(fwriter);
            fclose(fwriter);
          }

          memset(buffer, 0, YY_BUF_SIZE);
          n = -1;// n will be increased by 1 after this point
        }
	  }
      //END FOR
	  if ( c == EOF && ferror( stdin ) )
	  {
		 (void) fprintf( stderr, "%s\n", "input in flex scanner failed" );

		   exit( YY_EXIT_FAILURE );
	  }

	  if ( c == ';' ) {
	    buffer[n++] = (char) c;

		c = getc( stdin );

	    if ( c == '\n' )
		  buffer[n++] = (char) c;
	 }
	  if (is_first_round == 0)
	  {
        //save to file
        // printf("ok\n");
        /* FILE *fwriter;
	   fwriter = fopen(".oc_temp_hip", "w+");
	   fprintf(fwriter, "%s\n", buffer);
	   fflush(fwriter);
	   fclose(fwriter);
        */
        fwriter = fopen(".oc_temp_hip", "a");
         //fprintf(fwriter, "%s\n", buffer);
         fwrite(buffer, n, sizeof(char), fwriter);
        fflush(fwriter);
        fclose(fwriter);

       //rewind(fwriter);
	   yyin = fopen(".oc_temp_hip", "r");
	   //yyin = fwriter;
	   yy_switch_to_buffer(yy_create_buffer(yyin, n));
	   yyparse();
	   fclose(yyin);
	   fflush(stdout);
	  }
	  else
	  {
        //fclose(fwriter);
	    //buffer[n++] = (char) '\0';
		//buffer[n++] = (char) '\0';
	    //yy_switch_to_buffer(yy_scan_bytes(buffer, n+2));
	    yy_scan_bytes(buffer, n);
	    //yy_scan_buffer(buffer, n);
	    yyparse();
	    fflush(stdout);
      }
      // for debugging
      /* flog = fopen("oc_temp_locle", "a+"); */
      /* printf("#xxxx4\n");fprintf(flog, "%d", e); */
      /*  fflush(flog); */
      /*  fclose(flog); */
       //end for debugging
	/*else
	{
	  printf("%s: This command has not supported yet.\n", buffer);
      fflush(stdout);
	} */
   }
    //END WHILE
    // fprintf(fwriter, "%s\n", "BYTE");
    //		 fflush(fwriter);
	//	 fclose(fwriter);
  }
 /* fflush(DebugFile); */
 /* fclose(DebugFile); */
  //End
  
  
  delete globalDecls;
  foreach_map(cs,Const_String,r,Relation *,relationMap,
	      {delete r; relationMap[cs]=0;});

  return(0);
} /* end main */

namespace omega {

Relation LexForward(int n) {
  Relation r(n,n);
  F_Or *f = r.add_or();
  for (int i=1; i <= n; i++) {
	F_And *g = f->add_and();
	for(int j=1;j<i;j++) {
	   EQ_Handle e = g->add_EQ();
	   e.update_coef(r.input_var(j),-1);
	   e.update_coef(r.output_var(j),1);
	   e.finalize();
	   }
	GEQ_Handle e = g->add_GEQ();
	e.update_coef(r.input_var(i),-1);
	e.update_coef(r.output_var(i),1);
	e.update_const(-1);
	e.finalize();
	}
  r.finalize();
  return r;
  }

} // end of namespace omega

