/* $Id: match.c,v 1.2 2009-02-17 08:55:21 chinwn Exp $
 * -------------------------------------------------------
 * Copyright (c) 1998-2002 Sebastian Kienzl <zap@riot.org>
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

#include "match.h"
#include "muh.h"
#include "tools.h"

/* non-recursive caseinsensitive pattern-matching */
int match( char *string, char *pattern )
{
    char *str, *pat;

    if( !string || !pattern ) return 0;

    str = strdup( string );
    upcase( str );
    string = str;

    pat = strdup( pattern );
    upcase( pat );
    pattern = pat;

    while( 1 ) {
        if( !*string && !*pattern ) {
            FREE( str ); FREE( pat );
            return 1;
        }
        if( !*string || !*pattern ) {
            FREE( str ); FREE( pat );
            return 0;
        }

        if( *string == *pattern || ( *string && *pattern == '?' ) ) { string++; pattern++; }
        else
            if( *pattern == '*' ) {
                if( *string == *( pattern + 1 ) ) { pattern++; }
                else
                    if( *( pattern + 1 ) == *( string + 1 ) ) { string++; pattern++; }
                    else { string++; };
            }
            else {
                FREE( str ); FREE( pat );
                return 0;
            }
    }
}
