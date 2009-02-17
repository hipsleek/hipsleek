/* $Id: muh.h,v 1.2 2009-02-17 08:55:21 chinwn Exp $
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

#ifndef _MUH_H_
#define _MUH_H_

#include <config.h>

#define MUHRC "muhrc"
#define MUHDIR ".muh/"
#define FILE_PID "pid"
#define FILE_LOG "log"
#define FILE_MESSAGES "messages"

#define NICKSIZE 40
#ifndef VERSION
#define VERSION "2.xx"
#endif
#define DEFAULT_PORT 6667
#define BUFFERSIZE 1024

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>

#if HAVE_ERRNO_H
#include <errno.h>
#endif
#if HAVE_FCNTL_H
#include <fcntl.h>
#endif
#ifdef HAVE_SELECT_H
#include <sys/select.h>
#endif
#if HAVE_UNISTD_H
#include <unistd.h>
#endif
#if HAVE_SYS_TYPES_H
#include <sys/types.h>
#endif
#if HAVE_SYS_SOCKET_H
#include <sys/socket.h>
#endif
#if HAVE_SYS_STAT_H
#include <sys/stat.h>
#endif
#if HAVE_NETINET_IN_H
#include <netinet/in.h>
#endif
#if HAVE_NETDB_H
#include <netdb.h>
#endif
#if HAVE_ARPA_INET_H
#include <arpa/inet.h>
#endif
#if HAVE_SIGNAL_H
#include <signal.h>
#endif
#if HAVE_CTYPE_H
#include <ctype.h>
#endif
#if HAVE_STRINGS_H
#include <strings.h>
#endif
#if HAVE_CRYPT_H
#include <crypt.h>
#endif

#if TIME_WITH_SYS_TIME
# include <sys/time.h>
# include <time.h>
#else

# if HAVE_SYS_TIME_H
#  include <sys/time.h>
# else
#  include <time.h>
# endif
#endif

#if !HAVE_RANDOM
#define random() (rand()/16)
#endif

#if !HAVE_SIGACTION     /* old "weird signals" */
#define sigaction sigvec
#ifndef sa_handler
#define sa_handler sv_handler
#define sa_mask sv_mask
#define sa_flags sv_flags
#endif
#endif

#include "common.h"

typedef struct {
    char *nickname;
    int	got_nick;
    int	passok;
    int init;
    int	supress;
    int allowconnect;
    int allowreply;
    time_t startup;
    char *idhostname; /* ident@host where muh runs from */
} status_type;

typedef struct {
    int connected;
    char *nickname;
    char *username;
    char *hostname;
} client_info;

typedef struct {
    int	connected;
    char *realname;
    char *greeting[ 4 ];
    char *isupport[ 3 ];
    int current; /* index in servers.data[] */
} server_info;

typedef struct {
    int listenport;
    int logging;
    int leave;
    int getnick;
    int antiidle;
    int nevergiveup;
    int jumprestricted;
    int rejoin;
    int dccbounce;

    char *nickname;
    char *altnickname;
    char *awaynickname;
    char *awayreason;
    char *username;
    char *realname;
    char *password;
    char *home;
    char *leavemsg;
    char *bind;
    char *listenhost;
    char *awaynotice;
    char *forwardmsg;
    char *channels;
    char *dccbind;
    char *connectcmd;
    char *umodes;
} cfg_type;

typedef struct {
    char *name;
    int	port;
    char *password;
    int	working;
} server_type;

typedef struct {
    server_type **data;
    int amount;
} serverlist_type;

typedef struct {
    int	socket;
    int timer;
    char buffer[ BUFFERSIZE ]; /* don't worry */
    int	offset;
} connection_type;

typedef struct {
    int reply;
    int listen;
    int nickname;
    int antiidle;
    int forward;
} timer_type;

extern server_info i_server;
extern client_info i_client;
extern client_info i_newclient;

extern connection_type c_server;
extern connection_type c_client;
extern connection_type c_newclient;

extern cfg_type cfg;
extern status_type status;
extern serverlist_type servers;

extern FILE *messagelog;
void escape();
void read_cfg();
void drop_client( char *reason );
void drop_newclient( char *reason );
void drop_server( char *reason );
void drop_all( char *reason );
void server_next( int disablecurrent );
int proceed_timer( int *timer, int warn, int exceed );

/* parse-section */
/* config.l */
extern int lineno;
extern FILE *yyin;
void yyrestart( FILE * );

/* config.y */
int yyparse();

#endif
