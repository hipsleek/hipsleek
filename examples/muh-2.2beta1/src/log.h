/* $Id: log.h,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $
 * -------------------------------------------------------
 * Copyright (c) 2002 Lee Hardy <lee@leeh.co.uk>
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

#ifndef _LOG_H_
#define _LOG_H_

#include <stdio.h>
#include <stdlib.h>

#ifndef _DLINK_H_
#include "dlink.h"
#endif

#ifndef _CHANNELS_H_
#include "channels.h"
#endif

#define MAX_CHANNELS 40

#define LOG_JOINS	0x001
#define LOG_QUITS	0x002
#define LOG_EXITS	0x004
#define LOG_MODES	0x008
#define LOG_MESSAGES	0x010
#define LOG_NICKS	0x020
#define LOG_MISC	0x040
#define LOG_MUHCLIENT	0x080

#define LOG_ALL (LOG_JOINS|LOG_QUITS|LOG_EXITS|LOG_MODES|LOG_MESSAGES|LOG_NICKS|LOG_MISC|LOG_MUHCLIENT)

#define HAS_LOG(x, y) (((x)->log != NULL) && ((x)->log->logtype & y))

extern dlink_list log_list;
extern int global_logtype;

struct logentry
{
    char *channel;
    char *filename;
    int logtype;
};

extern void add_log(char *channel, char *logfile, int logtype);
extern void clear_logs(int);
extern void open_logs(void);

extern char *get_logtimestamp();

extern void write_logentry(struct channel *chptr, char *format, ...);
extern void write_logentry_all(int type, char *format, ...);
#endif

