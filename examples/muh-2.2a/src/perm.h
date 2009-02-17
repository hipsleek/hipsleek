/* $Id: perm.h,v 1.2 2009-02-17 08:55:21 chinwn Exp $
 * -------------------------------------------------------
 * Copyright (c) 1998-2000 Sebastian Kienzl <zap@riot.org>
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

#ifndef _PERM_H_
#define _PERM_H_

typedef struct {
    char *name;
    int allowed;
} perm_type;

typedef struct {
    perm_type **data;
    int amount;
} permlist_type;

void add_perm( permlist_type *table, char *name, int allowed );
void drop_perm( permlist_type *table );
int is_perm( permlist_type *table, char *name );

extern permlist_type hostlist;
extern permlist_type peoplelist;

#endif
