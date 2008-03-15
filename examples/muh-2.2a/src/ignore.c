/* $Id: ignore.c,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $
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
#include "ignore.h"
#include "table.h"

typedef struct {
    char *hostname;
    int ttl;
    int type;
} ignore_type;

typedef struct {
    ignore_type **data;
    int amount;
} ignores_type;

static void del_ignorebynumber(int i);
ignores_type ignores;

void add_ignore( char *hostname, int ttl, int type )
{
    int i, indx;

    if( !hostname ) return;
    for( i = 0; i < ignores.amount; i++ )
        if( ignores.data[ i ] &&
            ( xstrcmp( ignores.data[ i ]->hostname, hostname ) == 0 ) &&
            ( ignores.data[ i ]->type == type ) ) return;
    /* already in table? */

    ignores.data = ( ignore_type ** )add_item( ( void ** )ignores.data, sizeof( ignore_type ), &ignores.amount, &indx );
    ignores.data[ indx ]->hostname = strdup( hostname );
    ignores.data[ indx ]->ttl = ttl;
    ignores.data[ indx ]->type = type;
}

void del_ignore( char *hostname )
{
    int i;
    for( i = 0; i < ignores.amount; i++ )
        if( ignores.data[ i ] && ( xstrcmp( ignores.data[ i ]->hostname, hostname ) == 0 ) ) {
            xfree( ignores.data[ i ]->hostname );
            ignores.data = ( ignore_type ** )rem_item( ( void ** )ignores.data, i, &ignores.amount );
        }
}

void del_ignorebynumber( int i )
{
    if( i < ignores.amount && ignores.data[ i ] ) {
        xfree( ignores.data[ i ]->hostname );
        ignores.data = ( ignore_type ** )rem_item( ( void ** )ignores.data, i, &ignores.amount );
    }
}


void process_ignores()
{
    int i;
    for( i = 0; i < ignores.amount; i++ ) {
        if( ignores.data[ i ] ) {
            if( ignores.data[ i ]->ttl ) ignores.data[ i ]->ttl--;
            else del_ignorebynumber( i );
        }
    }
}

int is_ignore( char *hostname, int type )
{
    int i;
    for( i = 0; i < ignores.amount; i++ )
        if( ignores.data[ i ] &&
            ( xstrcmp( ignores.data[ i ]->hostname, hostname ) == 0 ) &&
            ( ignores.data[ i ]->type == type ) ) return 1;
    return 0;
}
