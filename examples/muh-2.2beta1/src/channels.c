/* $Id: channels.c,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $
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

#include "muh.h"
#include "channels.h"
#include "tools.h"
#include "dlink.h"
#include "table.h"
#include "log.h"
#include "messages.h"

dlink_list channel_list;

/* add_channel()
 *
 * adds a channel to muhs internal list
 */
void
add_channel(char *s)
{
    dlink_node *ptr;
    struct channel *chptr;
    struct logentry *logptr;

    /* check to see we're not trying to add a channel we're already in */
    for(ptr = channel_list.head; ptr; ptr = ptr->next)
    {
        chptr = ptr->data;
        if(xstrcmp(chptr->name, s) == 0)
	        return;
    }

    ptr = dlink_create();
    chptr = (struct channel *) xcalloc(1, sizeof(struct channel));
    dlink_add_tail(chptr, ptr, &channel_list);

    ptr->data = chptr;
    chptr->name = strdup(s);

    for(ptr = log_list.head; ptr; ptr = ptr->next)
    {
        logptr = ptr->data;

        if(xstrcasecmp(chptr->name, logptr->channel) == 0)
        {
            chptr->log = (struct channel_log *) xcalloc(1, sizeof(struct channel_log));
            chptr->log->logfile = fopen(logptr->filename, "a");
            
            /* error opening */
            if(chptr->log->logfile == NULL)
                return;

            chptr->log->logtype = logptr->logtype;
            write_logentry(chptr, LOGM_LOGOPEN, get_logtimestamp());
            return;
        }
    }

    if(global_logtype)
    {
        char *p;

        chptr->log = (struct channel_log *) xcalloc(1, sizeof(struct channel_log));
        p = xmalloc(strlen(chptr->name) + 5);
        sprintf(p, "%s.log", chptr->name);
        chptr->log->logfile = fopen(p, "a");

        if(chptr->log->logfile == NULL)
            return;

        chptr->log->logtype = global_logtype;
        write_logentry(chptr, LOGM_LOGOPEN, get_logtimestamp());
    }
}
    
/* rem_channel()
 *
 * removes a channel from muhs internal list
 */
void
rem_channel(struct channel *chptr)
{
    dlink_node *ptr;

    /* close the logfile if we have one */
    if(chptr->log != NULL)
    {
        if(chptr->log->logfile)
        {
            write_logentry(chptr, LOGM_LOGCLOSE, get_logtimestamp());
            fflush(chptr->log->logfile);
            fclose(chptr->log->logfile);
        }

        xfree(chptr->log);
    }

    if((ptr = dlink_find(chptr, &channel_list)) == NULL)
        return;

    dlink_delete(ptr, &channel_list);
    dlink_free(ptr);

    xfree(chptr->name);
    xfree(chptr->topic);
    xfree(chptr->topicwho);
    xfree(chptr->topicwhen);
    xfree(chptr);
}

/* drop_channels()
 *
 * removes all channel_list and topics from muhs internal list
 */
void
drop_channels()
{
    dlink_node *ptr;
    dlink_node *next_ptr;
    
    for(ptr = channel_list.head; ptr; ptr = next_ptr)
    {
        next_ptr = ptr->next;
        
        rem_channel((struct channel *)ptr->data);
    }
}

/* find_channel()
 *
 * searches for a channel, returning it if found, else NULL
 */
struct channel *
find_channel(char *name)
{
    dlink_node *ptr;
    struct channel *chptr;

    for(ptr = channel_list.head; ptr; ptr = ptr->next)
    {
        chptr = ptr->data;

        if(xstrcmp(chptr->name, name) == 0)
	        return chptr;
    }

    return NULL;
}

/* list_channels()
 *
 * returns a comma seperated list of all the channel_list we're in
 */
char *
list_channels()
{
    dlink_node *ptr;
    struct channel *chptr;
    static char temp[512];
    char *p;

    p = temp;

    for(ptr = channel_list.head; ptr; ptr = ptr->next)
    {
        chptr = ptr->data;
        p += sprintf(p, "%s,", chptr->name);
    }

    /* remove trailing , */
    p--;
    *p = '\0';
    return temp;
}

/* channel_topic()
 *
 * stores a topic for a channel we're in
 */
void
channel_topic(struct channel *chptr, char *topic)
{
    xfree(chptr->topic);
    xfree(chptr->topicwho);
    xfree(chptr->topicwhen);
    chptr->topic = NULL;
    chptr->topicwho = NULL;
    chptr->topicwhen = NULL;

    if(topic != NULL && *topic != '\0')
        chptr->topic = strdup(topic);
}

/* channel_when()
 *
 * stores who set the topic for a channel we're in
 */
void
channel_when(struct channel *chptr, char *topicwho, char *topicwhen)
{
    if(chptr->topic != NULL)
    {
        xfree(chptr->topicwho);
        xfree(chptr->topicwhen);

        chptr->topicwho = strdup(topicwho);
        chptr->topicwhen = strdup(topicwhen);
    }
}

/* hash_channel()
 *
 * creates a hash value based on the first 25 chars of a channel name
 */
unsigned int
hash_channel(char *p)
{
    int i = 25;
    unsigned int hash = 0;

    while(*p && --i)
	hash = (hash << 4) - (hash + (unsigned char)tolower(*p++));

    return (hash & (MAX_CHANNELS - 1));
}

