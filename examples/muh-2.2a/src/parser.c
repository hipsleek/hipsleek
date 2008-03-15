/* A Bison parser, made from parser.y, by GNU bison 1.75.  */

/* Skeleton parser for Yacc-like parsing with Bison,
   Copyright (C) 1984, 1989, 1990, 2000, 2001, 2002 Free Software Foundation, Inc.

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
   Foundation, Inc., 59 Temple Place - Suite 330,
   Boston, MA 02111-1307, USA.  */

/* As a special exception, when this file is copied by Bison into a
   Bison output file, you may use that output file without restriction.
   This special exception was added by the Free Software Foundation
   in version 1.24 of Bison.  */

/* Written by Richard Stallman by simplifying the original so called
   ``semantic'' parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON	1

/* Pure parsers.  */
#define YYPURE	0

/* Using locations.  */
#define YYLSP_NEEDED 0



/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     BOOLEAN = 258,
     NUMBER = 259,
     STRING = 260,
     NICKNAME = 261,
     REALNAME = 262,
     USERNAME = 263,
     SERVERS = 264,
     HOSTS = 265,
     PEOPLE = 266,
     LISTENPORT = 267,
     LISTENHOST = 268,
     PASSWORD = 269,
     ALTNICKNAME = 270,
     LOGGING = 271,
     LEAVE = 272,
     LEAVEMSG = 273,
     AWAY = 274,
     GETNICK = 275,
     BIND = 276,
     ANTIIDLE = 277,
     NEVERGIVEUP = 278,
     NORESTRICTED = 279,
     REJOIN = 280,
     FORWARDMSG = 281,
     CHANNELS = 282,
     DCCBOUNCE = 283,
     DCCBINDCLIENT = 284,
     CONNECTCMD = 285,
     UMODES = 286,
     AWAYNICKNAME = 287,
     AWAYREASON = 288,
     LOG = 289,
     TYPE = 290,
     CHANNEL = 291,
     LOGFILE = 292,
     L_JOINS = 293,
     L_EXITS = 294,
     L_QUITS = 295,
     L_MODES = 296,
     L_MESSAGES = 297,
     L_NICKS = 298,
     L_MISC = 299,
     L_MUHCLIENT = 300,
     L_ALL = 301
   };
#endif
#define BOOLEAN 258
#define NUMBER 259
#define STRING 260
#define NICKNAME 261
#define REALNAME 262
#define USERNAME 263
#define SERVERS 264
#define HOSTS 265
#define PEOPLE 266
#define LISTENPORT 267
#define LISTENHOST 268
#define PASSWORD 269
#define ALTNICKNAME 270
#define LOGGING 271
#define LEAVE 272
#define LEAVEMSG 273
#define AWAY 274
#define GETNICK 275
#define BIND 276
#define ANTIIDLE 277
#define NEVERGIVEUP 278
#define NORESTRICTED 279
#define REJOIN 280
#define FORWARDMSG 281
#define CHANNELS 282
#define DCCBOUNCE 283
#define DCCBINDCLIENT 284
#define CONNECTCMD 285
#define UMODES 286
#define AWAYNICKNAME 287
#define AWAYREASON 288
#define LOG 289
#define TYPE 290
#define CHANNEL 291
#define LOGFILE 292
#define L_JOINS 293
#define L_EXITS 294
#define L_QUITS 295
#define L_MODES 296
#define L_MESSAGES 297
#define L_NICKS 298
#define L_MISC 299
#define L_MUHCLIENT 300
#define L_ALL 301




/* Copy the first part of user declarations.  */
#line 1 "parser.y"

/* $Id: parser.c,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $
 * -------------------------------------------------------
 * Copyright (c) 1998-2002 Sebastian Kienzl <zap@riot.org>
 *           (c) 2002 Lee Hardy <lee@leeh.co.uk>
 * -------------------------------------------------------
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 */

#include <time.h>
#include "messages.h"
#include "tools.h"
#include "table.h"
#include "perm.h"
#include "log.h"
#include "common.h"

int yylex();
static int yyerror(char *);
static void add_server(char * name, int port, char *pass);

int lineno = 1;

int logtype = 0;
char *logchan;
char *logfilename;

permlist_type *permlist;

void add_server( char *name, int port, char *pass )
{
    int i, indx;

    if( !name ) return;
    if( !port ) port = DEFAULT_PORT;

    for( i = 0; i < servers.amount; i++ ) {
        if( ( strcmp( servers.data[ i ]->name, name ) == 0 ) &&
            ( servers.data[ i ]->port == port ) &&
            ( ( servers.data[ i ]->password == NULL ) == ( pass == NULL ) ) ) {
            if( name ) free( name );
            if( pass ) free( pass );
            return; /* server exists already */
        }
    }

    servers.data = ( server_type ** )add_item( ( void ** )servers.data, sizeof( server_type ), &servers.amount, &indx );
    servers.data[ indx ]->name = name;
    servers.data[ indx ]->port = port;
    servers.data[ indx ]->password = pass;
    servers.data[ indx ]->working = 1;
}

int yyerror( char *e )
{
    error( PARSE_SE, lineno );
    return 0;
}

#define ASSIGN_PARAM(x,y) { if(x) free(x); x=strdup(y); y=NULL; }



/* Enabling traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

#ifndef YYSTYPE
#line 72 "parser.y"
typedef union {
	int boolean;
	int number;
	char * string;
} yystype;
/* Line 193 of /usr/local/share/bison/yacc.c.  */
#line 242 "y.tab.c"
# define YYSTYPE yystype
# define YYSTYPE_IS_TRIVIAL 1
#endif

#ifndef YYLTYPE
typedef struct yyltype
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
} yyltype;
# define YYLTYPE yyltype
# define YYLTYPE_IS_TRIVIAL 1
#endif

/* Copy the second part of user declarations.  */


/* Line 213 of /usr/local/share/bison/yacc.c.  */
#line 263 "y.tab.c"

#if ! defined (yyoverflow) || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# if YYSTACK_USE_ALLOCA
#  define YYSTACK_ALLOC alloca
# else
#  ifndef YYSTACK_USE_ALLOCA
#   if defined (alloca) || defined (_ALLOCA_H)
#    define YYSTACK_ALLOC alloca
#   else
#    ifdef __GNUC__
#     define YYSTACK_ALLOC __builtin_alloca
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning. */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
# else
#  if defined (__STDC__) || defined (__cplusplus)
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   define YYSIZE_T size_t
#  endif
#  define YYSTACK_ALLOC malloc
#  define YYSTACK_FREE free
# endif
#endif /* ! defined (yyoverflow) || YYERROR_VERBOSE */


#if (! defined (yyoverflow) \
     && (! defined (__cplusplus) \
	 || (YYLTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  short yyss;
  YYSTYPE yyvs;
  };

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAX (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (short) + sizeof (YYSTYPE))				\
      + YYSTACK_GAP_MAX)

/* Copy COUNT objects from FROM to TO.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if 1 < __GNUC__
#   define YYCOPY(To, From, Count) \
      __builtin_memcpy (To, From, (Count) * sizeof (*(From)))
#  else
#   define YYCOPY(To, From, Count)		\
      do					\
	{					\
	  register YYSIZE_T yyi;		\
	  for (yyi = 0; yyi < (Count); yyi++)	\
	    (To)[yyi] = (From)[yyi];	\
	}					\
      while (0)
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
	yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAX;	\
	yyptr += yynewbytes / sizeof (*yyptr);				\
      }									\
    while (0)

#endif

#if defined (__STDC__) || defined (__cplusplus)
   typedef signed char yysigned_char;
#else
   typedef short yysigned_char;
#endif

/* YYFINAL -- State number of the termination state. */
#define YYFINAL  64
#define YYLAST   163

/* YYNTOKENS -- Number of terminals. */
#define YYNTOKENS  53
/* YYNNTS -- Number of nonterminals. */
#define YYNNTS  18
/* YYNRULES -- Number of rules. */
#define YYNRULES  65
/* YYNRULES -- Number of states. */
#define YYNSTATES  147

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   301

#define YYTRANSLATE(X) \
  ((unsigned)(X) <= YYMAXUTOK ? yytranslate[X] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const unsigned char yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,    51,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    52,    47,
       2,    48,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    49,     2,    50,     2,     2,     2,     2,
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
      45,    46
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const unsigned char yyprhs[] =
{
       0,     0,     3,     5,     8,    11,    14,    18,    22,    26,
      30,    34,    38,    43,    44,    50,    51,    57,    62,    66,
      70,    74,    78,    82,    86,    90,    94,    98,   102,   106,
     110,   114,   118,   122,   126,   130,   134,   138,   140,   144,
     146,   150,   156,   158,   162,   166,   169,   171,   173,   175,
     177,   179,   180,   186,   190,   192,   194,   196,   198,   200,
     202,   204,   206,   208,   210,   215
};

/* YYRHS -- A `-1'-separated list of the rules' RHS. */
static const yysigned_char yyrhs[] =
{
      54,     0,    -1,    55,    -1,    54,    55,    -1,    56,    47,
      -1,     1,    47,    -1,     6,    48,     5,    -1,    15,    48,
       5,    -1,    32,    48,     5,    -1,    33,    48,     5,    -1,
       7,    48,     5,    -1,     8,    48,     5,    -1,     9,    49,
      59,    50,    -1,    -1,    10,    57,    49,    61,    50,    -1,
      -1,    11,    58,    49,    61,    50,    -1,    34,    49,    63,
      50,    -1,    12,    48,     4,    -1,    13,    48,     5,    -1,
      14,    48,     5,    -1,    16,    48,     3,    -1,    17,    48,
       3,    -1,    18,    48,     5,    -1,    19,    48,     5,    -1,
      20,    48,     3,    -1,    21,    48,     5,    -1,    22,    48,
       3,    -1,    23,    48,     3,    -1,    24,    48,     3,    -1,
      25,    48,     3,    -1,    26,    48,     5,    -1,    27,    48,
       5,    -1,    28,    48,     3,    -1,    29,    48,     5,    -1,
      30,    48,     5,    -1,    31,    48,     5,    -1,    60,    -1,
      59,    51,    60,    -1,     5,    -1,     5,    52,     4,    -1,
       5,    52,     4,    52,     5,    -1,    62,    -1,    61,    51,
      62,    -1,     5,    52,     3,    -1,    63,    64,    -1,    64,
      -1,    65,    -1,    69,    -1,    70,    -1,     1,    -1,    -1,
      35,    66,    48,    67,    47,    -1,    67,    51,    68,    -1,
      68,    -1,    38,    -1,    39,    -1,    40,    -1,    41,    -1,
      42,    -1,    43,    -1,    44,    -1,    45,    -1,    46,    -1,
      36,    48,     5,    47,    -1,    37,    48,     5,    47,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const unsigned char yyrline[] =
{
       0,    95,    95,    96,    99,   100,   103,   107,   111,   115,
     116,   117,   118,   119,   119,   120,   120,   121,   126,   127,
     128,   129,   130,   131,   132,   133,   134,   135,   136,   137,
     138,   139,   140,   141,   142,   143,   144,   147,   148,   151,
     152,   153,   156,   157,   160,   163,   163,   166,   166,   166,
     166,   169,   168,   172,   172,   175,   177,   179,   181,   183,
     185,   187,   189,   191,   194,   199
};
#endif

#if YYDEBUG || YYERROR_VERBOSE
/* YYTNME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals. */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "BOOLEAN", "NUMBER", "STRING", "NICKNAME", 
  "REALNAME", "USERNAME", "SERVERS", "HOSTS", "PEOPLE", "LISTENPORT", 
  "LISTENHOST", "PASSWORD", "ALTNICKNAME", "LOGGING", "LEAVE", "LEAVEMSG", 
  "AWAY", "GETNICK", "BIND", "ANTIIDLE", "NEVERGIVEUP", "NORESTRICTED", 
  "REJOIN", "FORWARDMSG", "CHANNELS", "DCCBOUNCE", "DCCBINDCLIENT", 
  "CONNECTCMD", "UMODES", "AWAYNICKNAME", "AWAYREASON", "LOG", "TYPE", 
  "CHANNEL", "LOGFILE", "L_JOINS", "L_EXITS", "L_QUITS", "L_MODES", 
  "L_MESSAGES", "L_NICKS", "L_MISC", "L_MUHCLIENT", "L_ALL", "';'", "'='", 
  "'{'", "'}'", "','", "':'", "$accept", "statement_list", "statement", 
  "keywords", "@1", "@2", "server_list", "server", "perm_list", "perm", 
  "log_list", "log_item", "log_type", "@3", "log_typeitems", 
  "log_typeitem", "log_channel", "log_file", 0
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const unsigned short yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,    59,    61,   123,
     125,    44,    58
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const unsigned char yyr1[] =
{
       0,    53,    54,    54,    55,    55,    56,    56,    56,    56,
      56,    56,    56,    57,    56,    58,    56,    56,    56,    56,
      56,    56,    56,    56,    56,    56,    56,    56,    56,    56,
      56,    56,    56,    56,    56,    56,    56,    59,    59,    60,
      60,    60,    61,    61,    62,    63,    63,    64,    64,    64,
      64,    66,    65,    67,    67,    68,    68,    68,    68,    68,
      68,    68,    68,    68,    69,    70
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const unsigned char yyr2[] =
{
       0,     2,     1,     2,     2,     2,     3,     3,     3,     3,
       3,     3,     4,     0,     5,     0,     5,     4,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     3,     3,     3,
       3,     3,     3,     3,     3,     3,     3,     1,     3,     1,
       3,     5,     1,     3,     3,     2,     1,     1,     1,     1,
       1,     0,     5,     3,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     4,     4
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const unsigned char yydefact[] =
{
       0,     0,     0,     0,     0,     0,    13,    15,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     2,     0,     5,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     1,     3,     4,     6,    10,    11,
      39,     0,    37,     0,     0,    18,    19,    20,     7,    21,
      22,    23,    24,    25,    26,    27,    28,    29,    30,    31,
      32,    33,    34,    35,    36,     8,     9,    50,    51,     0,
       0,     0,    46,    47,    48,    49,     0,    12,     0,     0,
       0,    42,     0,     0,     0,     0,    17,    45,    40,    38,
       0,    14,     0,    16,     0,     0,     0,     0,    44,    43,
      55,    56,    57,    58,    59,    60,    61,    62,    63,     0,
      54,    64,    65,    41,    52,     0,    53
};

/* YYDEFGOTO[NTERM-NUM]. */
static const short yydefgoto[] =
{
      -1,    31,    32,    33,    39,    40,    71,    72,   110,   111,
     101,   102,   103,   113,   139,   140,   104,   105
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -50
static const short yypact[] =
{
      78,   -30,   -27,   -26,   -25,   -36,   -50,   -50,   -24,   -23,
     -22,   -21,   -20,   -19,   -18,   -17,   -16,   -15,    -8,    -7,
      -6,    -5,    -2,     0,    32,    33,    34,    35,    65,    66,
      67,    44,   -50,    68,   -50,    42,   112,   113,   114,    71,
      72,   118,   119,   120,   121,   124,   125,   126,   127,   130,
     129,   132,   133,   134,   135,   136,   137,   140,   139,   141,
     142,   143,   144,     2,   -50,   -50,   -50,   -50,   -50,   -50,
      77,   -49,   -50,   145,   145,   -50,   -50,   -50,   -50,   -50,
     -50,   -50,   -50,   -50,   -50,   -50,   -50,   -50,   -50,   -50,
     -50,   -50,   -50,   -50,   -50,   -50,   -50,   -50,   -50,    75,
      82,    -1,   -50,   -50,   -50,   -50,   147,   -50,   114,    87,
     -35,   -50,   -31,    92,   148,   149,   -50,   -50,    93,   -50,
     152,   -50,   145,   -50,   -34,   105,   109,   153,   -50,   -50,
     -50,   -50,   -50,   -50,   -50,   -50,   -50,   -50,   -50,   -33,
     -50,   -50,   -50,   -50,   -50,   -34,   -50
};

/* YYPGOTO[NTERM-NUM].  */
static const short yypgoto[] =
{
     -50,   -50,   128,   -50,   -50,   -50,   -50,    49,    86,    39,
     -50,    61,   -50,   -50,   -50,    18,   -50,   -50
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, parse error.  */
#define YYTABLE_NINF -1
static const unsigned char yytable[] =
{
      97,   107,   108,    97,   130,   131,   132,   133,   134,   135,
     136,   137,   138,    38,   144,   121,   122,    34,   145,   123,
     122,    35,    36,    37,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,    98,    99,   100,    98,    99,   100,
      51,    52,    53,    54,    64,     1,    55,    67,    56,   116,
       2,     3,     4,     5,     6,     7,     8,     9,    10,    11,
      12,    13,    14,    15,    16,    17,    18,    19,    20,    21,
      22,    23,    24,    25,    26,    27,    28,    29,    30,     1,
      57,    58,    59,    60,     2,     3,     4,     5,     6,     7,
       8,     9,    10,    11,    12,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    25,    26,    27,
      28,    29,    30,    61,    62,    66,    63,    68,    69,    70,
      73,    74,    75,   114,    76,    77,    78,    79,    80,   106,
     115,    81,    82,    83,    84,    85,    86,    87,    88,   120,
     124,    89,    90,    91,    92,   127,    93,    94,    95,    96,
     109,   118,   141,   125,   126,   128,   142,   119,   143,    65,
     112,   129,   117,   146
};

static const unsigned char yycheck[] =
{
       1,    50,    51,     1,    38,    39,    40,    41,    42,    43,
      44,    45,    46,    49,    47,    50,    51,    47,    51,    50,
      51,    48,    48,    48,    48,    48,    48,    48,    48,    48,
      48,    48,    48,    48,    35,    36,    37,    35,    36,    37,
      48,    48,    48,    48,     0,     1,    48,     5,    48,    50,
       6,     7,     8,     9,    10,    11,    12,    13,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    27,    28,    29,    30,    31,    32,    33,    34,     1,
      48,    48,    48,    48,     6,     7,     8,     9,    10,    11,
      12,    13,    14,    15,    16,    17,    18,    19,    20,    21,
      22,    23,    24,    25,    26,    27,    28,    29,    30,    31,
      32,    33,    34,    48,    48,    47,    49,     5,     5,     5,
      49,    49,     4,    48,     5,     5,     5,     3,     3,    52,
      48,     5,     5,     3,     5,     3,     3,     3,     3,    52,
      48,     5,     5,     3,     5,    52,     5,     5,     5,     5,
       5,     4,    47,     5,     5,     3,    47,   108,     5,    31,
      74,   122,   101,   145
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const unsigned char yystos[] =
{
       0,     1,     6,     7,     8,     9,    10,    11,    12,    13,
      14,    15,    16,    17,    18,    19,    20,    21,    22,    23,
      24,    25,    26,    27,    28,    29,    30,    31,    32,    33,
      34,    54,    55,    56,    47,    48,    48,    48,    49,    57,
      58,    48,    48,    48,    48,    48,    48,    48,    48,    48,
      48,    48,    48,    48,    48,    48,    48,    48,    48,    48,
      48,    48,    48,    49,     0,    55,    47,     5,     5,     5,
       5,    59,    60,    49,    49,     4,     5,     5,     5,     3,
       3,     5,     5,     3,     5,     3,     3,     3,     3,     5,
       5,     3,     5,     5,     5,     5,     5,     1,    35,    36,
      37,    63,    64,    65,    69,    70,    52,    50,    51,     5,
      61,    62,    61,    66,    48,    48,    50,    64,     4,    60,
      52,    50,    51,    50,    48,     5,     5,    52,     3,    62,
      38,    39,    40,    41,    42,    43,    44,    45,    46,    67,
      68,    47,    47,     5,    47,    51,    68
};

#if ! defined (YYSIZE_T) && defined (__SIZE_TYPE__)
# define YYSIZE_T __SIZE_TYPE__
#endif
#if ! defined (YYSIZE_T) && defined (size_t)
# define YYSIZE_T size_t
#endif
#if ! defined (YYSIZE_T)
# if defined (__STDC__) || defined (__cplusplus)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# endif
#endif
#if ! defined (YYSIZE_T)
# define YYSIZE_T unsigned int
#endif

#define yyerrok		(yyerrstatus = 0)
#define yyclearin	(yychar = YYEMPTY)
#define YYEMPTY		-2
#define YYEOF		0

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrlab1

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
      yychar1 = YYTRANSLATE (yychar);				\
      YYPOPSTACK;						\
      goto yybackup;						\
    }								\
  else								\
    { 								\
      yyerror ("syntax error: cannot back up");			\
      YYERROR;							\
    }								\
while (0)

#define YYTERROR	1
#define YYERRCODE	256

/* YYLLOC_DEFAULT -- Compute the default location (before the actions
   are run).  */

#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)           \
  Current.first_line   = Rhs[1].first_line;      \
  Current.first_column = Rhs[1].first_column;    \
  Current.last_line    = Rhs[N].last_line;       \
  Current.last_column  = Rhs[N].last_column;
#endif

/* YYLEX -- calling `yylex' with the right arguments.  */

#define YYLEX	yylex ()

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
} while (0)
# define YYDSYMPRINT(Args)			\
do {						\
  if (yydebug)					\
    yysymprint Args;				\
} while (0)
/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YYDSYMPRINT(Args)
#endif /* !YYDEBUG */

/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   SIZE_MAX < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#if YYMAXDEPTH == 0
# undef YYMAXDEPTH
#endif

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif



#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined (__GLIBC__) && defined (_STRING_H)
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
static YYSIZE_T
#   if defined (__STDC__) || defined (__cplusplus)
yystrlen (const char *yystr)
#   else
yystrlen (yystr)
     const char *yystr;
#   endif
{
  register const char *yys = yystr;

  while (*yys++ != '\0')
    continue;

  return yys - yystr - 1;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined (__GLIBC__) && defined (_STRING_H) && defined (_GNU_SOURCE)
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
#   if defined (__STDC__) || defined (__cplusplus)
yystpcpy (char *yydest, const char *yysrc)
#   else
yystpcpy (yydest, yysrc)
     char *yydest;
     const char *yysrc;
#   endif
{
  register char *yyd = yydest;
  register const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

#endif /* !YYERROR_VERBOSE */



#if YYDEBUG
/*-----------------------------.
| Print this symbol on YYOUT.  |
`-----------------------------*/

static void
#if defined (__STDC__) || defined (__cplusplus)
yysymprint (FILE* yyout, int yytype, YYSTYPE yyvalue)
#else
yysymprint (yyout, yytype, yyvalue)
    FILE* yyout;
    int yytype;
    YYSTYPE yyvalue;
#endif
{
  /* Pacify ``unused variable'' warnings.  */
  (void) yyvalue;

  if (yytype < YYNTOKENS)
    {
      YYFPRINTF (yyout, "token %s (", yytname[yytype]);
# ifdef YYPRINT
      YYPRINT (yyout, yytoknum[yytype], yyvalue);
# endif
    }
  else
    YYFPRINTF (yyout, "nterm %s (", yytname[yytype]);

  switch (yytype)
    {
      default:
        break;
    }
  YYFPRINTF (yyout, ")");
}
#endif /* YYDEBUG. */


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
#if defined (__STDC__) || defined (__cplusplus)
yydestruct (int yytype, YYSTYPE yyvalue)
#else
yydestruct (yytype, yyvalue)
    int yytype;
    YYSTYPE yyvalue;
#endif
{
  /* Pacify ``unused variable'' warnings.  */
  (void) yyvalue;

  switch (yytype)
    {
      default:
        break;
    }
}



/* The user can define YYPARSE_PARAM as the name of an argument to be passed
   into yyparse.  The argument should have type void *.
   It should actually point to an object.
   Grammar actions can access the variable by casting it
   to the proper pointer type.  */

#ifdef YYPARSE_PARAM
# if defined (__STDC__) || defined (__cplusplus)
#  define YYPARSE_PARAM_ARG void *YYPARSE_PARAM
#  define YYPARSE_PARAM_DECL
# else
#  define YYPARSE_PARAM_ARG YYPARSE_PARAM
#  define YYPARSE_PARAM_DECL void *YYPARSE_PARAM;
# endif
#else /* !YYPARSE_PARAM */
# define YYPARSE_PARAM_ARG
# define YYPARSE_PARAM_DECL
#endif /* !YYPARSE_PARAM */

/* Prevent warning if -Wstrict-prototypes.  */
#ifdef __GNUC__
# ifdef YYPARSE_PARAM
int yyparse (void *);
# else
int yyparse (void);
# endif
#endif


/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;

/* Number of parse errors so far.  */
int yynerrs;


int
yyparse (YYPARSE_PARAM_ARG)
     YYPARSE_PARAM_DECL
{
  
  register int yystate;
  register int yyn;
  int yyresult;
  /* Number of tokens to shift before error messages enabled.  */
  int yyerrstatus;
  /* Lookahead token as an internal (translated) token number.  */
  int yychar1 = 0;

  /* Three stacks and their tools:
     `yyss': related to states,
     `yyvs': related to semantic values,
     `yyls': related to locations.

     Refer to the stacks thru separate pointers, to allow yyoverflow
     to reallocate them elsewhere.  */

  /* The state stack.  */
  short	yyssa[YYINITDEPTH];
  short *yyss = yyssa;
  register short *yyssp;

  /* The semantic value stack.  */
  YYSTYPE yyvsa[YYINITDEPTH];
  YYSTYPE *yyvs = yyvsa;
  register YYSTYPE *yyvsp;



#define YYPOPSTACK   (yyvsp--, yyssp--)

  YYSIZE_T yystacksize = YYINITDEPTH;

  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;


  /* When reducing, the number of symbols on the RHS of the reduced
     rule.  */
  int yylen;

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
     have just been pushed. so pushing a state here evens the stacks.
     */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyssp >= yyss + yystacksize - 1)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
	/* Give user a chance to reallocate the stack. Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	YYSTYPE *yyvs1 = yyvs;
	short *yyss1 = yyss;


	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if yyoverflow is a macro.  */
	yyoverflow ("parser stack overflow",
		    &yyss1, yysize * sizeof (*yyssp),
		    &yyvs1, yysize * sizeof (*yyvsp),

		    &yystacksize);

	yyss = yyss1;
	yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyoverflowlab;
# else
      /* Extend the stack our own way.  */
      if (yystacksize >= YYMAXDEPTH)
	goto yyoverflowlab;
      yystacksize *= 2;
      if (yystacksize > YYMAXDEPTH)
	yystacksize = YYMAXDEPTH;

      {
	short *yyss1 = yyss;
	union yyalloc *yyptr =
	  (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
	if (! yyptr)
	  goto yyoverflowlab;
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

      if (yyssp >= yyss + yystacksize - 1)
	YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

/* Do appropriate processing given the current state.  */
/* Read a lookahead token if we need one and don't already have one.  */
/* yyresume: */

  /* First try to decide what to do without reference to lookahead token.  */

  yyn = yypact[yystate];
  if (yyn == YYPACT_NINF)
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* yychar is either YYEMPTY or YYEOF
     or a valid token in external form.  */

  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = YYLEX;
    }

  /* Convert token to internal form (in yychar1) for indexing tables with.  */

  if (yychar <= 0)		/* This means end of input.  */
    {
      yychar1 = 0;
      yychar = YYEOF;		/* Don't call YYLEX any more.  */

      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yychar1 = YYTRANSLATE (yychar);

      /* We have to keep this `#if YYDEBUG', since we use variables
	 which are defined only if `YYDEBUG' is set.  */
      YYDPRINTF ((stderr, "Next token is "));
      YYDSYMPRINT ((stderr, yychar1, yylval));
      YYDPRINTF ((stderr, "\n"));
    }

  /* If the proper action on seeing token YYCHAR1 is to reduce or to
     detect an error, take that action.  */
  yyn += yychar1;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yychar1)
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

  /* Shift the lookahead token.  */
  YYDPRINTF ((stderr, "Shifting token %d (%s), ",
	      yychar, yytname[yychar1]));

  /* Discard the token being shifted unless it is eof.  */
  if (yychar != YYEOF)
    yychar = YYEMPTY;

  *++yyvsp = yylval;


  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  yystate = yyn;
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



#if YYDEBUG
  /* We have to keep this `#if YYDEBUG', since we use variables which
     are defined only if `YYDEBUG' is set.  */
  if (yydebug)
    {
      int yyi;

      YYFPRINTF (stderr, "Reducing via rule %d (line %d), ",
		 yyn - 1, yyrline[yyn]);

      /* Print the symbols being reduced, and their result.  */
      for (yyi = yyprhs[yyn]; yyrhs[yyi] >= 0; yyi++)
	YYFPRINTF (stderr, "%s ", yytname[yyrhs[yyi]]);
      YYFPRINTF (stderr, " -> %s\n", yytname[yyr1[yyn]]);
    }
#endif
  switch (yyn)
    {
        case 5:
#line 100 "parser.y"
    { yyerrok; }
    break;

  case 6:
#line 103 "parser.y"
    {
                	if( strlen( yyvsp[0].string ) > NICKSIZE ) report( "WARNING: overlength nickname given\n" );
                	ASSIGN_PARAM( cfg.nickname, yyvsp[0].string );
		}
    break;

  case 7:
#line 107 "parser.y"
    {
                	if( strlen( yyvsp[0].string ) > NICKSIZE ) report( "WARNING: overlength altnickname given\n" );
                	ASSIGN_PARAM( cfg.altnickname, yyvsp[0].string );
		}
    break;

  case 8:
#line 111 "parser.y"
    {
                	if( strlen( yyvsp[0].string ) > NICKSIZE ) report( "WARNING: overlength awaynickname given\n" );
                	ASSIGN_PARAM( cfg.awaynickname, yyvsp[0].string );
		}
    break;

  case 9:
#line 115 "parser.y"
    { ASSIGN_PARAM( cfg.awayreason, yyvsp[0].string ); }
    break;

  case 10:
#line 116 "parser.y"
    { ASSIGN_PARAM( cfg.realname, yyvsp[0].string ); }
    break;

  case 11:
#line 117 "parser.y"
    { ASSIGN_PARAM( cfg.username, yyvsp[0].string ); }
    break;

  case 13:
#line 119 "parser.y"
    { permlist = &hostlist; drop_perm( permlist ); }
    break;

  case 15:
#line 120 "parser.y"
    { permlist = &peoplelist; drop_perm( permlist ); }
    break;

  case 17:
#line 121 "parser.y"
    {
				             add_log(logchan, logfilename, logtype);
					     FREE(logchan);
					     FREE(logfilename);
			             }
    break;

  case 18:
#line 126 "parser.y"
    { cfg.listenport = yyvsp[0].number; }
    break;

  case 19:
#line 127 "parser.y"
    { ASSIGN_PARAM( cfg.listenhost, yyvsp[0].string ); }
    break;

  case 20:
#line 128 "parser.y"
    { ASSIGN_PARAM( cfg.password, yyvsp[0].string ); }
    break;

  case 21:
#line 129 "parser.y"
    { cfg.logging = yyvsp[0].boolean; }
    break;

  case 22:
#line 130 "parser.y"
    { cfg.leave = yyvsp[0].boolean; }
    break;

  case 23:
#line 131 "parser.y"
    { ASSIGN_PARAM( cfg.leavemsg, yyvsp[0].string ); }
    break;

  case 24:
#line 132 "parser.y"
    { ASSIGN_PARAM( cfg.awaynotice, yyvsp[0].string ); }
    break;

  case 25:
#line 133 "parser.y"
    { cfg.getnick = yyvsp[0].boolean; }
    break;

  case 26:
#line 134 "parser.y"
    { ASSIGN_PARAM( cfg.bind, yyvsp[0].string ); }
    break;

  case 27:
#line 135 "parser.y"
    { cfg.antiidle = yyvsp[0].boolean; }
    break;

  case 28:
#line 136 "parser.y"
    { cfg.nevergiveup = yyvsp[0].boolean; }
    break;

  case 29:
#line 137 "parser.y"
    { cfg.jumprestricted = yyvsp[0].boolean; }
    break;

  case 30:
#line 138 "parser.y"
    { cfg.rejoin = yyvsp[0].boolean; }
    break;

  case 31:
#line 139 "parser.y"
    { ASSIGN_PARAM( cfg.forwardmsg, yyvsp[0].string ); }
    break;

  case 32:
#line 140 "parser.y"
    { ASSIGN_PARAM( cfg.channels, yyvsp[0].string ); }
    break;

  case 33:
#line 141 "parser.y"
    { cfg.dccbounce = yyvsp[0].boolean; }
    break;

  case 34:
#line 142 "parser.y"
    { ASSIGN_PARAM( cfg.dccbind, yyvsp[0].string ); }
    break;

  case 35:
#line 143 "parser.y"
    { ASSIGN_PARAM( cfg.connectcmd, yyvsp[0].string ); }
    break;

  case 36:
#line 144 "parser.y"
    { ASSIGN_PARAM( cfg.umodes, yyvsp[0].string ); }
    break;

  case 39:
#line 151 "parser.y"
    { add_server( yyvsp[0].string, 0, NULL ); }
    break;

  case 40:
#line 152 "parser.y"
    { add_server( yyvsp[-2].string, yyvsp[0].number, NULL ); }
    break;

  case 41:
#line 153 "parser.y"
    { add_server( yyvsp[-4].string, yyvsp[-2].number, yyvsp[0].string ); }
    break;

  case 44:
#line 160 "parser.y"
    { add_perm( permlist, yyvsp[-2].string, yyvsp[0].boolean ); }
    break;

  case 51:
#line 169 "parser.y"
    { logtype = 0; }
    break;

  case 55:
#line 176 "parser.y"
    { logtype |= LOG_JOINS; }
    break;

  case 56:
#line 178 "parser.y"
    { logtype |= LOG_EXITS; }
    break;

  case 57:
#line 180 "parser.y"
    { logtype |= LOG_QUITS; }
    break;

  case 58:
#line 182 "parser.y"
    { logtype |= LOG_MODES; }
    break;

  case 59:
#line 184 "parser.y"
    { logtype |= LOG_MESSAGES; }
    break;

  case 60:
#line 186 "parser.y"
    { logtype |= LOG_NICKS; }
    break;

  case 61:
#line 188 "parser.y"
    { logtype |= LOG_MISC; }
    break;

  case 62:
#line 190 "parser.y"
    { logtype |= LOG_MUHCLIENT; }
    break;

  case 63:
#line 192 "parser.y"
    { logtype |= LOG_ALL; }
    break;

  case 64:
#line 195 "parser.y"
    {
	logchan = strdup(yylval.string);
}
    break;

  case 65:
#line 200 "parser.y"
    {
	logfilename = strdup(yylval.string);
}
    break;


    }

/* Line 1016 of /usr/local/share/bison/yacc.c.  */
#line 1446 "y.tab.c"

  yyvsp -= yylen;
  yyssp -= yylen;


#if YYDEBUG
  if (yydebug)
    {
      short *yyssp1 = yyss - 1;
      YYFPRINTF (stderr, "state stack now");
      while (yyssp1 != yyssp)
	YYFPRINTF (stderr, " %d", *++yyssp1);
      YYFPRINTF (stderr, "\n");
    }
#endif

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
#if YYERROR_VERBOSE
      yyn = yypact[yystate];

      if (YYPACT_NINF < yyn && yyn < YYLAST)
	{
	  YYSIZE_T yysize = 0;
	  int yytype = YYTRANSLATE (yychar);
	  char *yymsg;
	  int yyx, yycount;

	  yycount = 0;
	  /* Start YYX at -YYN if negative to avoid negative indexes in
	     YYCHECK.  */
	  for (yyx = yyn < 0 ? -yyn : 0;
	       yyx < (int) (sizeof (yytname) / sizeof (char *)); yyx++)
	    if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR)
	      yysize += yystrlen (yytname[yyx]) + 15, yycount++;
	  yysize += yystrlen ("parse error, unexpected ") + 1;
	  yysize += yystrlen (yytname[yytype]);
	  yymsg = (char *) YYSTACK_ALLOC (yysize);
	  if (yymsg != 0)
	    {
	      char *yyp = yystpcpy (yymsg, "parse error, unexpected ");
	      yyp = yystpcpy (yyp, yytname[yytype]);

	      if (yycount < 5)
		{
		  yycount = 0;
		  for (yyx = yyn < 0 ? -yyn : 0;
		       yyx < (int) (sizeof (yytname) / sizeof (char *));
		       yyx++)
		    if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR)
		      {
			const char *yyq = ! yycount ? ", expecting " : " or ";
			yyp = yystpcpy (yyp, yyq);
			yyp = yystpcpy (yyp, yytname[yyx]);
			yycount++;
		      }
		}
	      yyerror (yymsg);
	      YYSTACK_FREE (yymsg);
	    }
	  else
	    yyerror ("parse error; also virtual memory exhausted");
	}
      else
#endif /* YYERROR_VERBOSE */
	yyerror ("parse error");
    }
  goto yyerrlab1;


/*----------------------------------------------------.
| yyerrlab1 -- error raised explicitly by an action.  |
`----------------------------------------------------*/
yyerrlab1:
  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
	 error, discard it.  */

      /* Return failure if at end of input.  */
      if (yychar == YYEOF)
        {
	  /* Pop the error token.  */
          YYPOPSTACK;
	  /* Pop the rest of the stack.  */
	  while (yyssp > yyss)
	    {
	      YYDPRINTF ((stderr, "Error: popping "));
	      YYDSYMPRINT ((stderr,
			    yystos[*yyssp],
			    *yyvsp));
	      YYDPRINTF ((stderr, "\n"));
	      yydestruct (yystos[*yyssp], *yyvsp);
	      YYPOPSTACK;
	    }
	  YYABORT;
        }

      YYDPRINTF ((stderr, "Discarding token %d (%s).\n",
		  yychar, yytname[yychar1]));
      yydestruct (yychar1, yylval);
      yychar = YYEMPTY;
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */

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

      YYDPRINTF ((stderr, "Error: popping "));
      YYDSYMPRINT ((stderr,
		    yystos[*yyssp], *yyvsp));
      YYDPRINTF ((stderr, "\n"));

      yydestruct (yystos[yystate], *yyvsp);
      yyvsp--;
      yystate = *--yyssp;


#if YYDEBUG
      if (yydebug)
	{
	  short *yyssp1 = yyss - 1;
	  YYFPRINTF (stderr, "Error: state stack now");
	  while (yyssp1 != yyssp)
	    YYFPRINTF (stderr, " %d", *++yyssp1);
	  YYFPRINTF (stderr, "\n");
	}
#endif
    }

  if (yyn == YYFINAL)
    YYACCEPT;

  YYDPRINTF ((stderr, "Shifting error token, "));

  *++yyvsp = yylval;


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
/*----------------------------------------------.
| yyoverflowlab -- parser overflow comes here.  |
`----------------------------------------------*/
yyoverflowlab:
  yyerror ("parser stack overflow");
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
  return yyresult;
}


#line 204 "parser.y"


