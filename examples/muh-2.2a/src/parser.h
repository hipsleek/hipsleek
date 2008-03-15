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

#ifndef BISON_Y_TAB_H
# define BISON_Y_TAB_H

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




#ifndef YYSTYPE
#line 72 "parser.y"
typedef union {
	int boolean;
	int number;
	char * string;
} yystype;
/* Line 1281 of /usr/local/share/bison/yacc.c.  */
#line 138 "y.tab.h"
# define YYSTYPE yystype
#endif

extern YYSTYPE yylval;


#endif /* not BISON_Y_TAB_H */

