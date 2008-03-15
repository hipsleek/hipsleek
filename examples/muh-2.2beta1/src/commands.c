/* $Id: commands.c,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $
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
#include <stdio.h>
#include "commands.h"
#include "common.h"

static struct CommandHash *cmd_hash[MAX_CMD];
static int hash_command(const char *p);
static void add_command(const char *p, int cmdvalue);

/* the struct for the command hash table */
struct CommandHash
{
    const char *cmd;
    int cmdvalue;
    struct CommandHash *next;
};

/* the struct for the table below */
struct CommandAddStruct
{
    char *cmd;
    int mask;
};

/* cmd_add_table[]
 *
 * the table of commands that we need to add at startup, and their
 * relevant bitmasks, as defined in commands.h
 */
static struct CommandAddStruct cmd_add_table[] =
{
    /* command,		bitmask,	*/
    { "PING",		CMD_PING,	},
    { "PONG",		CMD_PONG,	},
    { "MODE",		CMD_MODE,	},
    { "NICK",		CMD_NICK,	},
    { "NOTICE",		CMD_NOTICE,	},
    { "KICK",		CMD_KICK,	},
    { "JOIN",		CMD_JOIN,	},
    { "PART",		CMD_PART,	},
    { "TOPIC",		CMD_TOPIC,	},
    { "KILL",		CMD_KILL,	},
    { "PRIVMSG",	CMD_PRIVMSG,	},
    { "QUIT",		CMD_QUIT,	},
    { NULL,		CMD_NONE,	}
};

/* hash_command()
 *
 * hashes a command to a value
 */
static int hash_command(const char *p)
{
    int hash_val = 0;

    while(*p)
    {
        hash_val += ((int)(*p)&0xDF);
        p++;
    }

    return(hash_val % MAX_CMD);
}

/* find_command()
 *
 * searches for a command in the command hash table
 */
int find_command(char *p)
{
    struct CommandHash *ptr;
    int cmdindex;

    cmdindex = hash_command(p);

    for(ptr = cmd_hash[cmdindex]; ptr; ptr = ptr->next)
    {
        if(xstrcasecmp(p, ptr->cmd) == 0)
            return ptr->cmdvalue;
    }

    return 0;
}

/* add_command()
 *
 * adds a command to the command hash table
 */
void add_command(const char *cmd, int cmdvalue)
{
    struct CommandHash *ptr;
    struct CommandHash *temp_ptr;
    struct CommandHash *last_ptr = NULL;
    int cmdindex;

    cmdindex = hash_command(cmd);

    /* command exists */
    for(temp_ptr = cmd_hash[cmdindex]; temp_ptr; temp_ptr = temp_ptr->next)
    {
	if(xstrcasecmp(cmd, temp_ptr->cmd) == 0)
            return;

	last_ptr = temp_ptr;
    }

    ptr = (struct CommandHash *)xcalloc(1, sizeof(struct CommandHash));

    ptr->cmd = cmd;
    ptr->cmdvalue = cmdvalue;

    if(last_ptr)
	last_ptr->next = ptr;
    else
	cmd_hash[cmdindex] = ptr;
}

/* setup_commands()
 *
 * walks the commandsadd table and adds all the entries
 */
void setup_commands()
{
    int i;

    for(i = 0; cmd_add_table[i].cmd; i++)
	add_command(cmd_add_table[i].cmd, cmd_add_table[i].mask);
}
