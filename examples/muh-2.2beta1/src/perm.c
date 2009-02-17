/* $Id: perm.c,v 1.2 2009-02-17 08:55:22 chinwn Exp $
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
#include "perm.h"
#include "match.h"
#include "table.h"

void add_perm( permlist_type *table, char *name, int allowed )
{
    int indx;

    if( !name ) return;
    table->data = ( perm_type ** )add_item( ( void ** )table->data, sizeof( perm_type ), &table->amount, &indx );
    table->data[ indx ]->name = name;
    table->data[ indx ]->allowed = allowed;
}

void drop_perm( permlist_type *table )
{
    int i;
    for( i = 0; i < table->amount; i++ )
        FREE( table->data[ i ]->name );
    table->data = ( perm_type ** )free_table( ( void ** )table->data, &table->amount, 1 );
}

int is_perm( permlist_type *table, char *name )
{
    int i;

    for( i = 0; i < table->amount; i++ )
        if( match( name, table->data[ i ]->name ) ) return table->data[ i ]->allowed;

    return 1; /* default is yes */
}
