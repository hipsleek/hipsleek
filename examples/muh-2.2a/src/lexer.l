%{
/* $Id: lexer.l,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $
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

#include "parser.h"

extern int lineno;
extern int yylex(void);
char *s, *d;

%}

%option noyywrap
%option nounput
%x COMMENT

%%

[ \t]+          /* eat up whitespaces */

#.* |
"//".*		/* comment */
    
"/*"		{ BEGIN COMMENT; }
<COMMENT>"*/"  	{ BEGIN 0; }
<COMMENT>.	/* eat this */
<COMMENT>\n	lineno++;

config		{ yylval.boolean = 2; return BOOLEAN; }

yes |
enabled |
true		{ yylval.boolean = 1; return BOOLEAN; }

no |
disabled |
false		{ yylval.boolean = 0; return BOOLEAN; }


nick(name)?	{ return NICKNAME; }
altnick(name)?	{ return ALTNICKNAME; }
awaynick(name)?	{ return AWAYNICKNAME; }
awayreason	{ return AWAYREASON; }
realname	{ return REALNAME; }
username	{ return USERNAME; }
servers	        { return SERVERS; }
hosts	        { return HOSTS; }
people		{ return PEOPLE; }

listen(port)?	{ return LISTENPORT; }
listenhost	{ return LISTENHOST; }
pass(word)?	{ return PASSWORD; }

logging		{ return LOGGING; }
leave		{ return LEAVE; }
leavemsg	{ return LEAVEMSG; }
away		{ return AWAY; }
getnick		{ return GETNICK; }
bind		{ return BIND; }
antiidle	{ return ANTIIDLE; }
nevergiveup	{ return NEVERGIVEUP; }
norestricted	{ return NORESTRICTED; }
rejoin		{ return REJOIN; }
forwardmsg      { return FORWARDMSG; }
channels	{ return CHANNELS; }
connectcmd	{ return CONNECTCMD; }
umodes		{ return UMODES; }

bouncedcc      { return DCCBOUNCE; } /* for compatibility */
dccbounce      { return DCCBOUNCE; }
dccbindclient  { return DCCBINDCLIENT; }

log		{ return LOG; }
type		{ return TYPE; }
channel		{ return CHANNEL; }
logfile		{ return LOGFILE; }
joins		{ return L_JOINS; }
exits		{ return L_EXITS; }
quits		{ return L_QUITS; }
modes		{ return L_MODES; }
messages	{ return L_MESSAGES; }
nickchanges	{ return L_NICKS; }
misc		{ return L_MISC; }
muhclient	{ return L_MUHCLIENT; }
all		{ return L_ALL; }

[0-9]*          { 
    yylval.number = atoi( yytext );
    return NUMBER; 
}

\"[^\n"]*[\n"] {
    if( yytext[ yyleng - 2 ] == '\\' ) {
        yyless( yyleng - 1 );
        yymore();
    }
    else {
        yylval.string = malloc( yyleng + 1 );
        s = yytext + 1;
        d = yylval.string;

        while( *s ) {
            if( *s == '"' && *( s - 1 ) == '\\' )
                *( --d ) = *s;
            else
                *d = *s;
            d++; s++;
        }
        *( --d ) = 0;
        
        return STRING;
    }
}

\n		lineno++;

.		return yytext[ 0 ];

%%
