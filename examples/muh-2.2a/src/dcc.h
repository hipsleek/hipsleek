/* $Id: dcc.h,v 1.2 2009-02-17 08:55:21 chinwn Exp $
 * -------------------------------------------------------
 * Copyright (c) 1998-2001 Sebastian Kienzl <zap@riot.org>
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

#ifndef _DCC_H_
#define _DCC_H_

extern char* dcc_initiate( char* param, int fromclient );
extern void dcc_socketsubscribe( fd_set* readset, fd_set* writeset );
extern void dcc_socketcheck( fd_set* readset, fd_set* writeset );
extern void dcc_timer(); /* call every second! */

#endif
