/* $Id: tools.h,v 1.2 2009-02-17 08:55:21 chinwn Exp $
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

#ifndef _TOOLS_H_
#define _TOOLS_H_

void upcase( char *what );
void randname(char *randchar, int length);

int pos( char *str, char what );
int lastpos( char *str, char what );
char *lastword( char *from );
char *nextword( char *string );
char * gettimestamp();
char *gettimestamp2();
void getuptime(time_t, int *, int *, int *, int *);
void report( char *format, ... );
void error( char *format, ... );

#endif

