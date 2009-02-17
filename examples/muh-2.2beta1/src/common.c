/* $Id: common.c,v 1.2 2009-02-17 08:55:22 chinwn Exp $
 * -------------------------------------------------------
 * Copyright (c) 2002 Sebastian Kienzl <zap@riot.org>
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

#include <string.h>
#include <stdlib.h>
#include "muh.h"
#include "tools.h"
#include "messages.h"

#define REPORT_ERROR(func) error( ERR_UNEXPECTED, func, file, line );

int _xstrcmp( const char *s1, const char *s2 DEBUG_ADDPARMS )
{
	if( s1 && s2 )
		return strcmp( s1, s2 );
	else {
#ifdef DEBUG_ADDPARMS
		REPORT_ERROR( "xstrcmp" );
#endif
		return 1;
	}
}

int _xstrncmp( const char *s1, const char *s2, size_t n DEBUG_ADDPARMS )
{
	if( s1 && s2 )
		return strncmp( s1, s2, n );
	else {
#ifdef DEBUG_ADDPARMS
		REPORT_ERROR( "xstrncmp" );
#endif
		return 1;
	}
}

int _xstrcasecmp( const char *s1, const char *s2 DEBUG_ADDPARMS )
{
	if( s1 && s2 )
		return strcasecmp( s1, s2 );
	else {
#ifdef DEBUG_ADDPARMS
		REPORT_ERROR( "xstrcasecmp" );
#endif
		return 1;
	}
}

int _xstrncasecmp( const char *s1, const char *s2, size_t n DEBUG_ADDPARMS )
{
	if( s1 && s2 )
		return strncasecmp( s1, s2, n );
	else {
#ifdef DEBUG_ADDPARMS
		REPORT_ERROR( "xstrncasecmp" );
#endif
		return 1;
	}
}

char* _xstrcpy( char *dest, const char *src DEBUG_ADDPARMS )
{
	if( dest && src )
		return strcpy( dest, src );
	else {
#ifdef DEBUG_ADDPARMS
		REPORT_ERROR( "xstrcpy" );
#endif
		return 0;
	}
}

char* _xstrncpy( char *dest, const char *src, size_t n DEBUG_ADDPARMS )
{
	if( dest && src )
		return strncpy( dest, src, n );
	else {
#ifdef DEBUG_ADDPARMS
		REPORT_ERROR( "xstrncpy" );
#endif
		return 0;
	}
}

void * xmalloc( size_t size )
{
	void *ret = malloc( size );
	if( !ret ) {
		error( ERR_MEMORY );
		escape();
	}
	return ret;
}

void *xcalloc(size_t nmemb, size_t size)
{
	void *ret = calloc(nmemb, size);
	
	if(!ret)
	{
		error(ERR_MEMORY);
		escape();
	}

	return ret;
}

void xfree( void *ptr )
{
	if( ptr )
		free( ptr );
}

void * xrealloc( void *ptr, size_t size )
{
	void *ret = realloc( ptr, size );
	if( !ret && size ) {
		error( ERR_MEMORY );
		escape();
	}
	return ret;
}

