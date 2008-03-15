/* $Id: tools.c,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $
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
#include "tools.h"

void upcase( char *what )
{
    char *doit;
    if( what ) for( doit = what; doit && *doit; doit++ ) *doit = toupper( *doit );
}

void randname( char *randchar, int length )
{
    int i;
    if(randchar)
    {
        for( i = 0; i < length; i++ ) randchar[ i ] = ( char )( 'A' + ( rand() % 56 ) );
        randchar[ length ] = 0;
    }
}

int pos( char *str, char what )
{
    int i = 0;
    if( str ) {
        while( str[ i ] ) {
            if( str[ i ] == what ) return i;
            i++;
        }
    }
    return -1;
}

int lastpos( char *str, char what )
{
    int i;
    if( str ) {
        i = strlen( str ) - 1;
        while( i ) {
            if( str[ i ] == what ) return i;
            i--;
        }
    }
    return -1;
}

char *nextword( char *string )
{
    int i;
    if( ( i = pos( string, ' ' ) ) < 0 )
        return NULL;
    else
        return ( string + i + 1 );
}


char *lastword( char *from )
{
    int i;
    if( ( i = lastpos( from, ' ' ) ) < 0 )
        return from;
    else return from + i + 1;
}

/* gettimestamp()
 *
 * Creates a timestamp in the form:
 *    [Sun 21 Mar 11:23:12]
 */
char *gettimestamp()
{
    time_t t;
    struct tm *lt;
    static char stamp[ 100 ];

    time( &t );
    lt = localtime( &t );
    strftime( stamp, 99, "[%a %d %b %H:%M:%S]", lt );
    return stamp;
}

/* gettimestamp2()
 *
 * Creates a timestamp in the form:
 *     [11:23]
 */
char *gettimestamp2()
{
    time_t now;
    struct tm *form;
    static char stamp[8];

    time(&now);
    form = localtime(&now);
    strftime(stamp, 8, "[%H:%M]", form);
    return stamp;
}

void getuptime(time_t now, int *days, int *hours, 
	       int *minutes, int *seconds)
{
    *days = now / 86400;
    now %= 86400;
    *hours = now / 3600;
    now %= 3600;
    *minutes = now / 60;
    *seconds = now % 60;
}
	    
void report( char *format, ... )
{
    char buffer[ 150 ];
    va_list	va;

    va_start( va, format );
    vsnprintf( buffer, 149, format, va );
    va_end( va );
    fprintf( stdout, "%s + %s", gettimestamp(), buffer );
}

void error( char *format, ... )
{
    char buffer[ 150 ];
    va_list	va;

    va_start( va, format );
    vsnprintf( buffer, 149, format, va );
    va_end( va );
    fprintf( stdout, "%s - %s", gettimestamp(), buffer );
}

