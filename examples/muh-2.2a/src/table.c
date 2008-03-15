/* $Id: table.c,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $
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

#include "muh.h"
#include "table.h"

/* #define DEBUG */

/* c at it's best ;) */
void **add_item( void **data, int elementsize, int *entries, int *indx )
{
    int i;
    int ind = -1;

    for( i = 0; i < *entries; i++ ) {
        if( !data[ i ] ) {
            ind = i; /* xfree pointer found */
#ifdef DEBUG
            printf( "using empty pointer at index %d.\n", ind );
#endif
        }
    }
    if( ind < 0 ) { /* allocate new pointer */
        data = ( void ** )xrealloc( data, ++( *entries ) * sizeof( void * ) );
        ind = ( *entries - 1 );
#ifdef DEBUG
            printf( "allocating new pointer. %d entries, index %d\n", *entries, ind );
#endif
    }

    data[ ind ] = ( void * )xmalloc( elementsize );

    *indx = ind;

    return data;
}

void **compact_table( void **data, int *entries )
{
#ifdef DEBUG
    int x = 0;
#endif
    int i = *entries - 1;

    while( i >= 0 ) {
        if( !data[ i ] ) {
            data = ( void ** )xrealloc( data, --( *entries ) * sizeof( void * ) );
            if( !( *entries ) ) data = 0;
#ifdef DEBUG
            x++;
#endif
        }
        else
            i = -1;
        i--;
    }
#ifdef DEBUG
    printf( "reduced %d (size %d)\n", x, *entries );
    if( !*entries ) printf( "ignore: pointer-array is now empty\n" );
#endif
    return data;
}

void **rem_item( void **data, int number, int *entries )
{
    if( number >= 0 && number < *entries ) {
#ifdef DEBUG
        printf( "deleting entry %d, compacting table: ", number  );
#endif
        xfree( data[ number ] );
        data[ number ] = 0;
    }
    data = compact_table( data, entries );
    return data;
}

void **free_table( void **data, int *entries, int clear )
{
    int i;
    for( i = 0; i < *entries; i++ ) {
        if( data[ i ] ) xfree( data[ i ] );
    }
    xfree( data );

    if( clear )
      *entries = 0;

    return 0;
}
