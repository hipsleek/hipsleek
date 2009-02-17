/* $Id: irc.c,v 1.2 2009-02-17 08:55:22 chinwn Exp $
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

#include "muh.h"
#include "irc.h"
#include "perm.h"

/* #define DEBUG */

static void track_highest();
static void track_add(int s);
static void track_del(int s);

struct hostent *hostinfo;
#ifdef IPV6
struct sockaddr_in6 addr;
#else
struct sockaddr_in addr;
#endif

const char * net_errstr;

#define TRACK 512
int track_socks[ TRACK ];

int highest_socket = 0;

void track_highest()
{
    int i;
    highest_socket = 0;
    for( i = 0; i < TRACK; i++ )
        if( track_socks[ i ] > highest_socket ) highest_socket = track_socks[ i ];
}

void track_add( int s )
{
    int i = 0;
    while( track_socks[ i ] && i < TRACK ) i++;
    if( i < TRACK ) track_socks[ i ] = s;
    track_highest();
}

void track_del( int s )
{
    int i;
    for( i = 0; i < TRACK; i++ )
        if( track_socks[ i ] == s ) track_socks[ i ] = 0;
    track_highest();
}

int sock_open()
/* returns -1 on error, otherwise socket-number */
{
    int i;

#ifdef IPV6
    if( ( i = socket( AF_INET6, SOCK_STREAM, 0 ) ) < 0 )
#else
    if( ( i = socket( AF_INET, SOCK_STREAM, 0 ) ) < 0 )
#endif
    {
        net_errstr = strerror( errno );
        return -1;
    }
    track_add( i );
    sock_setreuse( i );
    /* local reuse by default */
    return i;
}

int rawsock_close(int sock)
{
    if(!sock)
        return 1;

    track_del(sock);
    close(sock);
    return 1;
}

int sock_close( connection_type *connection )
/* closes socket */
{
    rawsock_close(connection->socket);
    connection->socket = 0;
    return 1;
}


int sock_setnonblock(int sock)
{
    if(fcntl(sock, F_SETFL, O_NONBLOCK) < 0)
    {
        net_errstr = strerror( errno );
        return 0;
    }
    else
    {
        return 1;
    }
}

int sock_setblock(int sock)
{
    int flags;

    if((flags = fcntl(sock, F_GETFL, 0)) < 0)
    {
    	net_errstr = strerror( errno );
    	return 0;
    }

    flags &= ~O_NONBLOCK;

    if(fcntl(sock, F_SETFL, flags) < 0)
    {
        net_errstr = strerror( errno );
        return 0;
    }

    return 1;
}

int sock_setreuse(int sock)
{
    int i = 1;
    if(setsockopt(sock, SOL_SOCKET, SO_REUSEADDR, (void *)&i, sizeof(i)) < 0)
    {
        net_errstr = strerror( errno );
        return 0;
    }
    else
    {
        return 1;
    }
}

struct hostent *name_lookup( char *host )
{
#ifdef IPV6
    if((hostinfo = gethostbyname2(host, AF_INET6)))
        return hostinfo;
#else
    if((hostinfo = gethostbyname(host)))
        return hostinfo;
#endif
    else
    {
#ifdef HAVE_HSTRERROR
        net_errstr = ( const char * )hstrerror( h_errno );
#else
	net_errstr = "unable to resolve";
#endif
        return NULL;
    }
}

#ifdef IPV6
int sock_bind(int sock, char *bindhost, int port)
{
    bzero(&addr, sizeof(struct sockaddr_in6));

    addr.sin6_addr = in6addr_any;
    addr.sin6_family = AF_INET6;

    if(bindhost)
    {
        if(!name_lookup(bindhost))
            return 0;

        memcpy((char *)&addr.sin6_addr, hostinfo->h_addr, hostinfo->h_length);
        addr.sin6_family = hostinfo->h_addrtype;
    }

    addr.sin6_port = htons((u_short)port);

    if(bind(sock, (struct sockaddr *)&addr, sizeof(struct sockaddr_in6)) < 0)
    {
        net_errstr = strerror(errno);
        return 0;
    }

    return 1;
}

int sock_bindlookedup(int sock, int port)
{
    bzero(&addr, sizeof(struct sockaddr_in6));

    addr.sin6_addr = in6addr_any;
    addr.sin6_family = AF_INET6;

    if(hostinfo)
    {
        memcpy((char *)&addr.sin6_addr, hostinfo->h_addr, hostinfo->h_length);
	addr.sin6_family = hostinfo->h_addrtype;
    }

    addr.sin6_port = htons((u_short)port);

    if(bind(sock, (struct sockaddr *)&addr, sizeof(struct sockaddr_in6)) < 0)
    {
        net_errstr = strerror(errno);
	return 0;
    }

    return 1;
}

#else

int sock_bind( int sock, char *bindhost, int port )
{
    bzero( &addr, sizeof( struct sockaddr_in ) );

    addr.sin_addr.s_addr = INADDR_ANY;
    addr.sin_family = AF_INET;

    if( bindhost )
    {
        if( !name_lookup( bindhost ) )
            return 0;

        memcpy( ( char * )&addr.sin_addr, hostinfo->h_addr, hostinfo->h_length );
        addr.sin_family = hostinfo->h_addrtype;
    }

    addr.sin_port = htons( ( u_short )port );

    if( bind( sock, ( struct sockaddr * )&addr, sizeof( struct sockaddr ) ) < 0 )
    {
	net_errstr = strerror( errno ); return 0;
    }

    return 1;
}

int sock_bindlookedup( int sock, int port )
{
    bzero( &addr, sizeof( struct sockaddr_in ) );

    addr.sin_addr.s_addr = INADDR_ANY;
    addr.sin_family = AF_INET;

    if( hostinfo )
    {
        memcpy( ( char * )&addr.sin_addr, hostinfo->h_addr, hostinfo->h_length );
        addr.sin_family = hostinfo->h_addrtype;
    }

    addr.sin_port = htons( ( u_short )port );

    if( bind( sock, ( struct sockaddr * )&addr, sizeof( struct sockaddr ) ) < 0 )
    {
        net_errstr = strerror( errno );
        return 0;
    }
    return 1;
}
#endif

int sock_listen(int sock)
{
    if(!sock_setnonblock(sock))
	return 0;

    if(listen(sock, 5) < 0)
    {
        net_errstr = strerror(errno);
        return 0;
    }
    return 1;
}

int sock_accept(int sock, char **s, int checkperm)
{
    int temp;
    int store;
#ifdef IPV6
    char ip[40];
    char ipv6[512];
#else
    char *ip;
#endif
    int perm;

#ifdef IPV6
    temp = sizeof( struct sockaddr_in6 );
#else
    temp = sizeof( struct sockaddr_in );
#endif
    if( ( store = accept( sock, ( struct sockaddr * )&addr, &temp ) ) < 0 )
    {
        net_errstr = strerror( errno );
        return 0;
    }

#ifdef IPV6
    inet_ntop( AF_INET6, (char *)&addr.sin6_addr, ip, sizeof( addr.sin6_addr ) );
#else
    ip = inet_ntoa( addr.sin_addr );
#endif
    perm = is_perm( &hostlist, ip );

#ifdef IPV6
    if(!getnameinfo( (struct sockaddr *) &addr, sizeof(addr), ipv6, sizeof(ipv6), 0, 0, 0) )
    {
        *s = strdup( ipv6 );
	perm |= is_perm( &hostlist, *s );
    }
    else
        *s = strdup( ip );

#else

    hostinfo = gethostbyaddr( ( char * )&addr.sin_addr.s_addr, sizeof( struct in_addr ), AF_INET );

    if( hostinfo ) {
        *s = strdup( hostinfo->h_name );
        perm |= is_perm( &hostlist, *s );
    }
    else *s = strdup( ip );
#endif

    if(!checkperm || perm)
    {
        track_add( store );
        return store;
    }
    else
    {
        close( store );
        return -1;
    }
}

int irc_write( connection_type *connection, char *format, ... )
{
    va_list va;
    char buffer[ BUFFERSIZE ];

    va_start( va, format );
    vsnprintf( buffer, BUFFERSIZE - 3, format, va );
    va_end( va );
    strcat( buffer, "\r\n" );
#ifdef DEBUG
    fprintf( stdout, ">>%03d>> %s", connection->socket, buffer );
#endif
    return write( connection->socket, buffer, strlen( buffer ) );
}

void irc_privmsg( connection_type *connection, char nickname[], char *format, ... )
{
    va_list va;
    char buffer[ BUFFERSIZE ];

    va_start( va, format );
    vsnprintf( buffer, BUFFERSIZE - 10, format, va );
    va_end( va );

    irc_write( connection, "PRIVMSG %s :%s", nickname, buffer );
}

void irc_notice( connection_type *connection, char nickname[], char *format, ... )
{
    va_list va;
    char buffer[ BUFFERSIZE ];

    va_start( va, format );
    vsnprintf( buffer, BUFFERSIZE - 10, format, va );
    va_end( va );

    irc_write( connection, "NOTICE %s :%s", nickname, buffer );
}

int irc_read( connection_type *connection )
/* -1 -> fehler; 0 -> keine daten (falls non-blocking); 1 -> daten */
{
    int ret;
    connection->timer = 0;
    do {
	ret = read( connection->socket, connection->buffer + connection->offset, 1 );
	if( ret == 0 ) return -1; /* EOF */
	if( ret == -1 && errno == EAGAIN ) return 0;
        connection->offset++;
    } while( connection->buffer[ connection->offset - 1 ] != '\n' && connection->offset < ( BUFFERSIZE - 4 ) );
    connection->buffer[ connection->offset - 1 ] = 0; /* lf raus! */
    if( connection->buffer[ connection->offset - 2 ] == '\r' ) connection->buffer[ connection->offset - 2 ] = 0;
    /* bei servern immer, bei clients nicht */
#ifdef DEBUG
    fprintf( stdout, "<<%03d<< %s\n", connection->socket, connection->buffer );
#endif
    connection->offset = 0;
    return 1;
}

int irc_connect( connection_type *connection, server_type *server, char *nickname, char *username, char *realname, char *bindto )
/* returns:
 0..........allright
 1..........kein socket konnte kreiert werden
 2..........server konnte nicht resolved werden
 3..........konnte nicht binden
 4..........tcp/ip-connection zum server konnte nicht eröffnet werden
 5..........write failed
 6..........anderer fehler
 */
{
    int randport = 0, ri, attempts;

    connection->timer = 0;

    if( ( connection->socket = sock_open() ) < 0 )
        return 1;

    hostinfo = 0;
    if( bindto ) {
        if( !name_lookup( bindto ) ) return 3;
    }

    attempts = 15;
    do {
        for( ri = random() & 0xff; ri; ri-- )
            randport = ( random() & 0xffff ) | 1024;
#ifdef IPV6
        addr.sin6_port = htons( randport );
#else
        addr.sin_port = htons( randport );
#endif
        attempts--;
    } while( !sock_bindlookedup( connection->socket, randport ) && attempts );

    if( !attempts ) return 3;

    if( !name_lookup( server->name ) ) return 2;

#ifdef IPV6
    memcpy( (char *)&addr.sin6_addr, hostinfo->h_addr, hostinfo->h_length );
    addr.sin6_port = htons( (u_short)server->port );
    addr.sin6_family = hostinfo->h_addrtype;
    if( connect( connection->socket, ( struct sockaddr * )&addr, sizeof( struct sockaddr_in6 ) ) < 0 ) return 4;
#else
    memcpy( ( char * )&addr.sin_addr, hostinfo->h_addr, hostinfo->h_length );
    addr.sin_port = htons( ( u_short )server->port );
    addr.sin_family = hostinfo->h_addrtype;
    if( connect( connection->socket, ( struct sockaddr * )&addr, sizeof( struct sockaddr_in ) ) < 0 ) return 4;
#endif

    if( server->password ) irc_write( connection, "PASS %s", server->password );
    if( irc_write( connection, "NICK %s", nickname ) < 0 ) return 5;
    if( irc_write( connection, "USER %s +i %s :%s", username, server->name, realname ) < 0 ) return 5;
    if( !sock_setnonblock( connection->socket ) ) return 6;
    return 0;
}

