/* $Id: irc.h,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $
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

#ifndef _IRC_H_
#define _IRC_H_

#include "muh.h"

extern int highest_socket;
extern const char * net_errstr;

/* all these function return 0 on error (except sock_open, this will return -1)
 * on error net_errstr will point to the error_string
 */
int sock_open();
int sock_close( connection_type *connection );
int sock_listen(int sock);
int sock_setnonblock(int sock);
int sock_setblock(int sock);
int sock_setreuse(int sock);
int sock_bind(int sock, char *bindhost, int port);
int sock_bindlookedup(int sock, int port);
int sock_accept(int sock, char **hostname, int checkperm);

/* this one returns -1 if hostname is not permitted to connect */
int rawsock_close(int sock);
struct hostent *name_lookup(char *bindhost);

int irc_write( connection_type *connection, char *format, ... );
/* returns: on success -> number of written bytes; -1 on error */

int irc_read( connection_type *connection );
/* returns: 1/0(no data (if blocking)) on success; -1 on error */

int irc_connect( connection_type *connection, server_type *server, char *nickname, char *username, char *realname, char *bindto );
/* returns: 0 on success
 * errors: 1 - sock_open() failed
 *         2 - remotelookup failed
 *         3 - unable to bind
 *         4 - connect() failed
 *         5 - write() failed
 *         6 - other error
 * IMPORTANT! connection->connected does NOT get set!
 */

void irc_privmsg( connection_type *connection, char nickname[], char *format, ... );
void irc_notice( connection_type *connection, char nickname[], char *format, ... );


/* v IRC-REPLY-CODES */

#define RPL_WELCOME 1
#define RPL_YOURHOST 2
#define RPL_SERVERIS 3
#define RPL_SERVERVER 4
#define RPL_ISUPPORT 5

#define RPL_MOTDSTART 375
#define RPL_MOTD 372
#define RPL_ENDOFMOTD 376

#define RPL_LUSERCLIENT 251
#define RPL_LUSEROP 252
#define RPL_LUSERUNKNOWN 253
#define RPL_LUSERCHANNELS 254
#define RPL_LUSERME 255

#define RPL_NOTOPIC 331
#define RPL_TOPIC 332
#define RPL_TOPICWHO 333

#define ERR_ERRONEUSNICKNAME 432
#define ERR_NICKNAMEINUSE 433
#define ERR_NICKUNAVAILABLE 437
#define ERR_NOPERMFORHOST 463
#define ERR_YOUREBANNEDCREEP 465

#define RPL_RESTRICTED 484

#define RPL_WHOISUSER 311
#define RPL_WHOISSERVER 312
#define RPL_WHOISOPERATOR 313
#define RPL_WHOISIDLE 317
#define RPL_WHOISCHANNELS 319
#define RPL_ENDOFWHOIS 318

#endif
