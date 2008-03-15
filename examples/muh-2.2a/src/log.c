/* $Id: log.c,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $
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

#include <string.h>
#include "log.h"
#include "muh.h"
#include "messages.h"

int global_logtype;
dlink_list log_list;

/* add_log()
 *
 * called from config file parser, creates a logging entry in the hashtable
 */
void
add_log(char *log_channel, char *logfile, int logtype)
{
    char *channel;
    int multi = 0;

    /* damn people playing with us! :) */
    if(!log_channel || *log_channel == '\0')
        return;

    /* the "global" logentry, mark the logtype and then open logfiles
     * for channels we dont have specific entries for
     */
    if(xstrcmp(log_channel, "*") == 0)
    {
        global_logtype = logtype;
        return;
    }

    /* if we're doing multi channels, mark as such so we dont use a 
     * specified logfile, revert to #channel.log
     */
    if((strchr(log_channel, ',')))
        multi = 1;

    for(channel = strtok(log_channel, ","); channel; channel = strtok(NULL, ","))
    {
        dlink_node *ptr;
        struct logentry *logptr;

        /* check we havent already done this channel */
        for(ptr = log_list.head; ptr; ptr = ptr->next)
        {
            logptr = ptr->data;
            if(xstrcasecmp(channel, logptr->channel) == 0)
                return;
        }

        ptr = dlink_create();
        logptr = (struct logentry *) xcalloc(1, sizeof(struct logentry));
        dlink_add(logptr, ptr, &log_list);

        logptr->channel = strdup(channel);
        logptr->logtype = logtype;

        /* if were not given a logfile, create one, xmalloc it and as this has
         * its own memory, we can point ptr->filename to it
         */
        if(!logfile || multi)
        {
            char *temp_log;
            temp_log = xmalloc(strlen(channel) + 5);
            sprintf(temp_log, "%s.log", channel);
       	    logptr->filename = temp_log;
        }
        else
        {
            logptr->filename = strdup(logfile);
        }
    }
} 

void
open_logs(void)
{
    dlink_node *ptr;
    dlink_node *lptr;
    struct channel *chptr;
    struct logentry *logptr;

    for(ptr = channel_list.head; ptr; ptr = ptr->next)
    {
        chptr = ptr->data;

        if(chptr->log != NULL)
            continue;

        for(lptr = log_list.head; lptr; lptr = lptr->next)
        {
            logptr = lptr->data;

            if(xstrcasecmp(chptr->name, logptr->channel) == 0)
            {
                chptr->log = (struct channel_log *) xcalloc(1, sizeof(struct channel_log));
                chptr->log->logfile = fopen(logptr->filename, "a");

                if(chptr->log->logfile == NULL)
                    return;

                chptr->log->logtype = logptr->logtype;
                write_logentry(chptr, LOGM_LOGOPEN, get_logtimestamp());
                continue;
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
}

void
clear_logs(int clear)
{
    dlink_node *ptr;
    dlink_node *next_ptr;
    struct channel *chptr;
    struct logentry *logptr;

    /* first, close all the open logfiles in the channels */
    for(ptr = channel_list.head; ptr; ptr = next_ptr)
    {
        next_ptr = ptr->next;
        chptr = ptr->data;
        
        if(chptr->log == NULL)
            continue;

        write_logentry(chptr, LOGM_LOGCLOSE, get_logtimestamp());
        fclose(chptr->log->logfile);

        xfree(chptr->log);
        chptr->log = NULL;
    }

    if(clear == 0)
        return;

    /* then clear the loglist */
    for(ptr = log_list.head; ptr; ptr = next_ptr)
    {
        next_ptr = ptr->next;
        logptr = ptr->data;

        xfree(logptr->channel);
        xfree(logptr->filename);
        xfree(logptr);

        dlink_delete(ptr, &log_list);
        dlink_free(ptr);
    }
}

/* write_logentry()
 *
 * writes a logging entry to the logfile
 */
void
write_logentry(struct channel *chptr, char *format, ...)
{
    char buffer[1024];
    va_list va;

    /* no logfile for this channel */
    if((chptr->log == NULL) || (chptr->log->logfile == NULL))
        return;
    
    va_start(va, format);
    vsnprintf(buffer, 1023, format, va);
    va_end(va);

    fprintf(chptr->log->logfile, "%s", buffer);
    fflush(chptr->log->logfile);
}

/* write_logentry_all()
 *
 * writes a logging entry to all matching logfiles
 */
void
write_logentry_all(int type, char *format, ...)
{
    dlink_node *ptr;
    struct channel *chptr;
    char buffer[1024];
    va_list va;

    va_start(va, format);
    vsnprintf(buffer, 1023, format, va);
    va_end(va);

    for(ptr = channel_list.head; ptr; ptr = ptr->next)
    {
	    chptr = ptr->data;

        if((chptr->log == NULL) || (chptr->log->logfile == NULL))
            continue;

        if(chptr->log->logtype & type)
    	    write_logentry(chptr, "%s", buffer);
	
    }
}

/* get_logtimestamp()
 *
 * creates a timestamp in the form:
 *    Sun Jan 02 11:53:33 2002
 */
char *
get_logtimestamp()
{
    time_t now;
    struct tm *form;
    static char stamp[100];

    time(&now);
    form = localtime(&now);
    strftime(stamp, 99, "%a %b %d %H:%M:%S %Y", form);
    return stamp;
}

