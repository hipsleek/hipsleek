%{
/* $Id: parser.y,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $
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

%}

%union {
	int boolean;
	int number;
	char * string;
}

%token <boolean> BOOLEAN
%token <number> NUMBER
%token <string> STRING

%token NICKNAME REALNAME USERNAME SERVERS HOSTS PEOPLE
%token LISTENPORT LISTENHOST PASSWORD ALTNICKNAME
%token LOGGING LEAVE LEAVEMSG AWAY GETNICK
%token BIND ANTIIDLE NEVERGIVEUP NORESTRICTED
%token REJOIN FORWARDMSG CHANNELS
%token DCCBOUNCE DCCBINDCLIENT

%token LOG TYPE CHANNEL LOGFILE
%token L_JOINS L_EXITS L_QUITS L_MODES L_MESSAGES L_NICKS L_MISC L_MUHCLIENT L_ALL
%%

statement_list:	statement
	|	statement_list statement
        ;

statement:	keywords ';'
	|	error ';' 				{ yyerrok; }
        ;

keywords:	NICKNAME '=' STRING {
                	if( strlen( $3 ) > NICKSIZE ) report( "WARNING: overlength nickname given\n" );
                	ASSIGN_PARAM( cfg.nickname, $3 );
		}
	|	ALTNICKNAME '=' STRING {
                	if( strlen( $3 ) > NICKSIZE ) report( "WARNING: overlength altnickname given\n" );
                	ASSIGN_PARAM( cfg.altnickname, $3 );
		}        		
        |	REALNAME '=' STRING			{ ASSIGN_PARAM( cfg.realname, $3 ); }
        |	USERNAME '=' STRING			{ ASSIGN_PARAM( cfg.username, $3 ); }
	|	SERVERS '{' server_list '}'
	|	HOSTS { permlist = &hostlist; drop_perm( permlist ); } '{' perm_list '}'
        |	PEOPLE { permlist = &peoplelist; drop_perm( permlist ); } '{' perm_list '}'
	|	LOG '{' log_list '}' {
				             add_log(logchan, logfilename, logtype);
					     FREE(logchan);
					     FREE(logfilename);
			             }
        |	LISTENPORT '=' NUMBER			{ cfg.listenport = $3; }
	|	LISTENHOST '=' STRING			{ ASSIGN_PARAM( cfg.listenhost, $3 ); }
        |	PASSWORD '=' STRING			{ ASSIGN_PARAM( cfg.password, $3 ); }
        |	LOGGING '=' BOOLEAN			{ cfg.logging = $3; }
        |	LEAVE '=' BOOLEAN			{ cfg.leave = $3; }
        |	LEAVEMSG '=' STRING			{ ASSIGN_PARAM( cfg.leavemsg, $3 ); }
        |	AWAY '=' STRING      			{ ASSIGN_PARAM( cfg.awaynotice, $3 ); }
        |	GETNICK '=' BOOLEAN			{ cfg.getnick = $3; }
        |	BIND '=' STRING       			{ ASSIGN_PARAM( cfg.bind, $3 ); }
        |	ANTIIDLE '=' BOOLEAN 			{ cfg.antiidle = $3; }
        |	NEVERGIVEUP '=' BOOLEAN			{ cfg.nevergiveup = $3; }
        |	NORESTRICTED '=' BOOLEAN		{ cfg.jumprestricted = $3; }
        |	REJOIN '=' BOOLEAN			{ cfg.rejoin = $3; }
        |	FORWARDMSG '=' STRING			{ ASSIGN_PARAM( cfg.forwardmsg, $3 ); }
	|	CHANNELS '=' STRING			{ ASSIGN_PARAM( cfg.channels, $3 ); }
	|	DCCBOUNCE '=' BOOLEAN			{ cfg.dccbounce = $3; }
	|	DCCBINDCLIENT '=' STRING		{ ASSIGN_PARAM( cfg.dccbind, $3 ); }
	;

server_list:	server
	|      	server_list ',' server
        ;

server:		STRING 					{ add_server( $1, 0, NULL ); }
	|	STRING ':' NUMBER 			{ add_server( $1, $3, NULL ); }
	|	STRING ':' NUMBER ':' STRING 		{ add_server( $1, $3, $5 ); }
	;

perm_list:	perm
	|	perm_list ',' perm
        ;
        
perm:		STRING ':' BOOLEAN			{ add_perm( permlist, $1, $3 ); }
        ;

log_list:	log_list log_item |
		log_item;

log_item:	log_type | log_channel | log_file | error;

log_type:	TYPE
			{ logtype = 0; }
		'=' log_typeitems ';' ;

log_typeitems:	log_typeitems ',' log_typeitem |
		log_typeitem;

log_typeitem:	L_JOINS
			{ logtype |= LOG_JOINS; }
		| L_EXITS
			{ logtype |= LOG_EXITS; }
		| L_QUITS
			{ logtype |= LOG_QUITS; }
		| L_MODES
			{ logtype |= LOG_MODES; }
		| L_MESSAGES
			{ logtype |= LOG_MESSAGES; }
		| L_NICKS
			{ logtype |= LOG_NICKS; }
		| L_MISC
			{ logtype |= LOG_MISC; }
		| L_MUHCLIENT
			{ logtype |= LOG_MUHCLIENT; }
		| L_ALL
			{ logtype |= LOG_ALL; };

log_channel:	CHANNEL '=' STRING ';'
{
	logchan = strdup(yylval.string);
};

log_file:	LOGFILE '=' STRING ';'
{
	logfilename = strdup(yylval.string);
};

%%
