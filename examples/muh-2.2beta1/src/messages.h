/* $Id: messages.h,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $
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

#ifndef _MESSAGES_H_
#define _MESSAGES_H_

/*
 * general
 */
#define FNF "unable to open file '%s'!\n"

#define SYNTAX "\
Usage: %s [-f] [-c] [-d dir]\n\n \
    -f\t\tstay in foreground\n \
    -d dir\tother directory than default for muh-files\n \
    -c\t\tcreate crypted password\n\n"

/*
 * parsing-section
 */
#define PARSE_SE "parse error on line %d!\n"
#define PARSE_MK "'%s' has not been set!\n"
#define PARSE_NOSERV "no servers have been specified!\n"

/*
 * muh-messages
 */
#define MUH_PARSING "parsing configuration file...\n"
#define MUH_ERRCFG "unable to open muhrc in %s!\n"
#define MUH_ERRNEEDARG "option -%c requires an argument!\n"
#define MUH_ERRNOHOME "$HOME is not set! (set it or use -d)\n"
#define MUH_ERRFILE "can't write to %s!\n"
#define MUH_ERRCHDIR "can't chdir to %s!\n"
#define MUH_ERREXIT "terminating...\n"
#define MUH_SIGTERM "caught sigterm, terminating...\n"
#define MUH_OUTOFSERVERS "i'm out of servers, terminating...\n"
#define MUH_OUTOFSERVERSNEVER "i'm out of servers but i won't give up...\n"
#define MUH_ERRFORK "unable to fork!\n"
#define MUH_FORKED "alrite, muh's forked. (pid %d)\n"
#define MUH_ERRMSGFILE "can't open msgfile, won't log anything i get!\n"
#define MUH_LEAVING "leaving channels...\n"
#define MUH_REINTRODUCE "reintroducing channels...\n"
#define MUH_REJOINING "rejoining channels (%s)...\n"
#define MUH_JOINING "autojoining channels (%s)...\n"
#define MUH_JUMP "changing server..."
#define MUH_RECONNECT "reconnecting to server..."
#define MUH_DIE_CL "ouch."
#define MUH_DIE "dying...\n"
#define MUH_REHASH "rehashing..."
#define MUH_RESET "resetting all servers to working.."
#define MUH_UPTIME "muh has been online: %dd %02dh %02dm %02ds\n"
#define MUH_NICK "muh's nick is '%s'.\n"
#define MUH_GOTNICK "cool, got nick '%s'!\n"
#define MUH_NEWSESSION "---------- NEW SESSION ----------\n"
#define MUH_STARTINGLOG "muh version "VERSION" - starting log...\n"

#define MUH_ENTERPASS "Enter password to crypt: "
#define MUH_THISPASS "Set this as password in your muhrc: %s\n\n"

#define BANNER "\
-=======================================================-\n\
 muh v"VERSION" -- http://mind.riot.org/muh/\n\
 Copyright (c) 1998-2002 Sebastian Kienzl <zap@riot.org>\n\
                    2002 Lee Hardy <lee@leeh.co.uk>\n\
-=======================================================-\n\
     This program comes with ABSOLUTELY NO WARRANTY!\n\
      This is free software, and you are welcome to\n\
        redistribute it under certain conditions.\n\
              For details, read 'COPYING'.\n\
-=======================================================-\n\n"

/*
 * socket-messages
 */
#define SOCK_GENERROR "general socket error (%s)!\n"
#define SOCK_ERROPEN "unable to create socket!\n"
#define SOCK_ERRBIND "unable to bind to port %d!\n"
#define SOCK_ERRBINDHOST "unable to bind to '%s':%d!\n"
#define SOCK_ERRLISTEN "unable to listen!\n"
#define SOCK_ERRACCEPT "unable to accept connection from '%s'!\n"
#define SOCK_LISTENOK "listening on port %d.\n"
#define SOCK_LISTENOKHOST "listening on host %s/port %d.\n"
#define SOCK_CONNECT "tcp-connection to '%s' established!\n"
#define SOCK_ERRRESOLVE "unable to resolve '%s'!\n"
#define SOCK_ERRCONNECT "unable to connect to '%s'! (%s)\n"
#define SOCK_ERRWRITE "error while sending data to '%s'!\n"
#define SOCK_RECONNECT "trying to reconnect to '%s' in 5 seconds...\n"

/*
 * irc-messages
 */
#define IRC_CONNECTED "connected to '%s'.\n"
#define IRC_ERRIN "'%s' is a invalid nickname - terminating!\n"
#define IRC_NICKINUSE "nickname '%s' is in use - using nickname '%s'.\n"
#define IRC_NICKUNAVAIL "nickname '%s' is unavailable - using nickname '%s'.\n"
#define IRC_SERVERERROR "server-error! (%s)\n"
#define IRC_KILL "you've been killed by '%s'!\n"

/*
 * client-related-messages
 */
#define CLNT_AUTHFAIL "authorisation failed, dropping new client!\n"
#define CLNT_AUTHTO "new client timed out in authorisation state!\n"
#define CLNT_AUTHFAILNOTICE "Unsuccessful connect-attempt from '%s'!"
#define CLNT_AUTHOK "authorisation successful!\n"
#define CLNT_DROP "dropped old client.\n"
#define CLNT_LEFT "client signed off.\n"
#define CLNT_STONED "disconnected stoned client.\n"

#define CLNT_HAVEMSGS "\2You have messages.\2 (/MUH READ)"
#define CLNT_HAVENOMSGS "You don't have any messages!"
#define CLNT_KILLEDMSGS "Killed your messages."

#define CLNT_CAUGHT "caught client from '%s'.\n"
#define CLNT_RECONNECT "reconnection-attempt from '%s'.\n"
#define CLNT_DENIED "denied client from '%s'.\n"
#define CLNT_DROPPED "client dropped connection.\n"
#define CLNT_DROPPEDUNAUTH "client dropped connection in authorisation-state.\n"

#define CLNT_CTCP "received a CTCP %s from %s.\n"
#define CLNT_CTCPNOREPLY "received a CTCP %s from %s. (didn't reply)\n"
#define CLNT_KICK "%s kicked me out of %s (%s)!\n"

/*
 * server-related-messages
 */
#define SERV_ERR "closed connection after server reported error.\n"
#define SERV_STONED "disconnecting from stoned server.\n"
#define SERV_TRYING "trying server '%s' on port %d...\n"
#define SERV_DROPPED "server dropped connection!\n"
#define SERV_RESTRICTED "connection is restricted, jumping...\n"


/*
 * client-side-messages
 */
#define VERSIONREPLY "\1VERSION muh v"VERSION" (http://mind.riot.org/muh)\1"
#define TIMEREPLY "\1TIME %s\1"
#define USERINFOREPLY "\1USERINFO weiss-hellbraun gefleckt, milchgebend.\1"
#define CLIENTINFOREPLY "\1CLIENTINFO GIBMILCH MUH KACK FURZ WIEDERKAEU BRUNZ LAUF SCHWANZWEDEL FRISS SAUF LECK\1"
#define FINGERREPLY "\1FINGER point that fucking finger up your ass!\1"

#define CLNT_COMANDS "Available commands: HELP READ DEL JUMP REHASH RESET DIE PRINT UPTIME"
#define CLNT_MSGLOGSTART "Playing messagelog..."
#define CLNT_MSGLOGEND "End of messagelog."
#define CLNT_NEWCLIENT "New connection established!"
#define CLNT_MESSAGES "you have messages waiting. (read them with /muh read)"
#define CLNT_NOMESSAGES "you have no messages waiting."
#define CLNT_RESTRICTED "restricted connection"
#define CLNT_SLIST "Printing serverlist..."
#define CLNT_CURRENT "Current server is %d."

#define DCC_SUCCESS "dcc: bounce from %s established! [%d]\n"
#define DCC_TIMEOUT "dcc: bounce timed out! [%d]\n"
#define DCC_ERRCONNECT "dcc: can't connect peer! (%s) [%d]\n"
#define DCC_ERRACCEPT "dcc: can't accept incoming! (%s) [%d]\n"
#define DCC_ERRSOCK "dcc: socket-error! (%s) [%d]\n"
#define DCC_START "dcc: starting bounce to %s:%d! [%d]\n"
#define DCC_END "dcc: ending bounce [%d]\n"

#define LOGM_JOIN "%s *** %s!%s has joined %s\n"
#define LOGM_PART "%s *** %s has left %s (%s)\n"
#define LOGM_QUIT "%s *** %s has quit IRC (%s %s)\n"
#define LOGM_KICK "%s *** %s was kicked by %s (%s)\n"
#define LOGM_MODES "%s *** %s sets mode %s\n"
#define LOGM_PRIVMSG "%s <%s> %s\n"
#define LOGM_NOTICE "%s -%s:%s- %s\n"
#define LOGM_TOPIC "%s *** %s changes topic to '%s'\n"
#define LOGM_NICK "%s *** %s is now known as %s\n"
#define LOGM_MUH "%s *** client has %sconnected\n"
#define LOGM_LOGOPEN "Session Start: %s\n"
#define LOGM_LOGCLOSE "Session Close: %s\n\n"

/*
 * general error-message
 */
#define ERR_MEMORY "out of memory, terminating!\n"
#define ERR_UNEXPECTED "!!! an unexpected situation occured, please send us this: [%s, %s:%d]\n"

#endif

