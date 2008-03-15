/* $Id: channels.h,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $
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

#ifndef _CHANNELS_H_
#define _CHANNELS_H_

#include <stdio.h>
#include <stdlib.h>

#ifndef _DLINK_H_
#include "dlink.h"
#endif

struct channel_log
{
    int logtype;
    FILE *logfile;
};

struct channel
{
    char *name;
    char *topic;
    char *topicwho;
    char *topicwhen;
    struct channel_log *log;
};

struct dlink_list;
extern dlink_list channel_list;

void add_channel(char *s);
void rem_channel(struct channel *);
void drop_channels();
struct channel *find_channel(char *);
char *list_channels();

void channel_topic(struct channel *, char *);
void channel_when(struct channel *, char *, char *);

extern unsigned int hash_channel(char *);

#endif

