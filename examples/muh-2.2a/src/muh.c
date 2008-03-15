/* $Id: muh.c,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $
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

/* #define DEBUG */

#include "muh.h"
#include "irc.h"
#include "tools.h"
#include "messages.h"
#include "ignore.h"
#include "channels.h"
#include "perm.h"
#include "ascii.h"
#include "commands.h"
#include "dcc.h"
#include "log.h"

FILE *messagelog = NULL;

static int read_server();
static int read_newclient();
static int read_client();
static int checkconfig();

static void fakeconnect();
static void sig_term();
static void create_listen();
static void rehash();
static void client_left();
static void check_timers();
static void run();
static void init();

static void server_reset();
static void setup_home(char *s);
static void muh_commands(char *command, char *param);
static void server_commands(char *command, char *param, int *pass);
static void server_reply_num(int command, char *origin, char *param1,
		             char *param2, int *pass);
static void server_reply_str(char *command, char *origin, char *param1,
		             char *param2, int *pass);


status_type status;
cfg_type cfg = {
    0, /* listenport */
    1, /* logging */
    1, /* leave */
    1, /* getnick */
    0, /* antiidle */
    0, /* nevergiveup */
    0, /* jumprestricted */
    0, /* rejoin */
    0, /* dccbounce */
    NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL, NULL /* string-pointers */
};

permlist_type hostlist;
permlist_type peoplelist;
serverlist_type servers;
timer_type timers;

/*****verbindungs-bezogene variablen*************/
server_info i_server;
client_info i_client;
client_info i_newclient;

connection_type c_server;
connection_type c_client;
connection_type c_newclient;

int listensocket = 0;  	/* listensocket */
char *forwardmsg = NULL;
const char* muh_binary;


void escape()
{
    rawsock_close( listensocket );
    sock_close( &c_server );
    sock_close( &c_client );
    sock_close( &c_newclient );
    if( messagelog ) fclose( messagelog );
    unlink( FILE_PID );
    error( MUH_ERREXIT );
    exit( 1 );
}

void read_cfg()
{
    lineno = 1;
    report( MUH_PARSING );
    if( !( yyin = fopen( MUHRC, "r" ) ) ) {
        error( MUH_ERRCFG, cfg.home );
        escape();
    }
    yyrestart( yyin );
    if( yyparse() ) {
        fclose( yyin );
        escape();
    }
    fclose( yyin );
}

void sig_term()
{
    error(MUH_SIGTERM);
    escape();
}

void drop_client( char *reason )
{
    if( i_client.connected ) {
        if( reason ) {
            /* set back to blocking */
            sock_setblock( c_server.socket );
            if( reason[ 0 ] == ':' )
                irc_write( &c_client, "ERROR %s", reason );
            else
                irc_write( &c_client, "ERROR :Closing Link: %s", reason );
        }
        sock_close( &c_client );
        i_client.connected = 0;
    }
}

void drop_newclient( char *reason )
{
    if( i_newclient.connected ) {
        if( reason ) {
            sock_setblock( c_server.socket );
            irc_write( &c_newclient, "ERROR :Closing Link: %s", reason );
        }
        sock_close( &c_newclient );
        i_newclient.connected = 0;
        status.init = 0;
    }
}

void drop_server( char *reason )
{
    if( c_server.socket ) { /* die abfrage _SO_ lassen */
        if( reason )
	{
            sock_setblock( c_server.socket );
            irc_write( &c_server, "QUIT :%s", reason );

	    write_logentry_all(LOG_QUITS, LOGM_QUIT,
			       gettimestamp2(), status.nickname, reason, "");
        }
        sock_close( &c_server );
    }
    i_server.connected = 0;

    if(!cfg.rejoin)
        drop_channels(); /* we don't want to rejoin */
}

void drop_all( char *reason )
{
    drop_server( reason );
    drop_client( reason );
    drop_newclient( NULL ); /* this ain't newclients' business */
}

/* server_reset()
 *
 * resets all servers to 'working'
 */
void server_reset()
{
    int i;

    for(i = 0; i < servers.amount; i++)
    {
	servers.data[i]->working = 1;
    }
}
void server_next( int disablecurrent )
{
    int i = i_server.current;
    int x;

    if( disablecurrent ) servers.data[ i_server.current ]->working = 0;

    do {
        i_server.current++;
        if( i_server.current >= servers.amount ) i_server.current = 0;
    } while( !servers.data[ i_server.current ]->working && ( i_server.current != i ) );

    if( !servers.data[ i_server.current ]->working ) {
        if( cfg.nevergiveup ) {
            report( MUH_OUTOFSERVERSNEVER );
            for( x = 0; x < servers.amount; x++ )
                servers.data[ x ]->working = 1;
            i_server.current = 0;
        }
        else {
            error( MUH_OUTOFSERVERS );
            escape();
        }
    }

    if( i == i_server.current ) {
        report( SOCK_RECONNECT, servers.data[ i_server.current ]->name );
        sleep( 5 );
    }
}

int proceed_timer( int *timer, int warn, int exceed )
{
    (*timer)++;
    if( *timer == warn ) return 1;
    if( *timer >= exceed ) {
        *timer = 0;
        return 2;
    }
    return 0;
}

void create_listen()
{
    if( listensocket ) rawsock_close( listensocket );

    /* creating listener */
    if( ( listensocket = sock_open() ) < 0 ) {
        error( SOCK_ERROPEN );
        escape();
    }

    if( !sock_bind( listensocket, cfg.listenhost, cfg.listenport ) ) {
        if( cfg.listenhost )
            error( SOCK_ERRBINDHOST, cfg.listenhost, cfg.listenport );
	else
            error( SOCK_ERRBIND, cfg.listenport );
        escape();
    }

    if( !sock_listen( listensocket ) ) {
        error( SOCK_ERRLISTEN );
        escape();
    }

    if( cfg.listenhost )
        report( SOCK_LISTENOKHOST, cfg.listenhost, cfg.listenport );
    else
        report( SOCK_LISTENOK, cfg.listenport );
    /* .. end */
}

void rehash()
{
    char *oldnick;
    char *oldlistenhost;
    char *oldrealname;
    char *oldusername;
    int oldlistenport;

    report( MUH_REHASH"\n" );

    oldnick = strdup( cfg.nickname );
    oldusername = strdup( cfg.username );
    oldrealname = strdup( cfg.realname );
    oldlistenport = cfg.listenport;
    if( cfg.listenhost )
        oldlistenhost = strdup( cfg.listenhost );
    else
        oldlistenhost = NULL;

    clear_logs(1);
    read_cfg();
    open_logs();

    if( xstrcmp( oldnick, cfg.nickname ) ) status.got_nick = 0;

    if( ( oldlistenport != cfg.listenport ) ||
        ( ( oldlistenhost == NULL ?
            ( cfg.listenhost == NULL ? 0 : 1 ) : ( cfg.listenhost == NULL ?
                                             1 : xstrcmp( oldlistenhost, cfg.listenhost ) ) ) ) )
        create_listen();

    if( !cfg.logging && messagelog ) {
        fclose( messagelog );
        messagelog = NULL;
    }

    if( cfg.logging && !messagelog ) {
        if( !( messagelog = fopen( FILE_MESSAGES, "a+" ) ) ) {
            report( MUH_ERRMSGFILE );
        }
    }

    if( xstrcmp( oldrealname, cfg.realname ) || xstrcmp( oldusername, cfg.username ) ) {
        drop_all( MUH_RECONNECT );
        report( MUH_RECONNECT"\n" );
        i_server.current--;
        sleep( 5 );
        server_next( 0 );
    }

    FREE( oldnick );
    FREE( oldrealname );
    FREE( oldusername );
    FREE( oldlistenhost );
}

void client_left()
{
    char *chns;

    if( ( chns = list_channels() ) ) {
        if( cfg.leavemsg ) irc_write( &c_server, "PRIVMSG %s :\1ACTION %s\1", chns, cfg.leavemsg );
        if(cfg.leave)
	{
            report(MUH_LEAVING);
            irc_write(&c_server, "JOIN 0");
        }
	else
	    write_logentry_all(LOG_MUHCLIENT, LOGM_MUH, gettimestamp2(), "dis");
	/* set away */
	if (cfg.awayreason)
	    irc_write(&c_server, "AWAY :%s", cfg.awayreason);
	/* switch to away nickname */
	if (cfg.awaynickname)
	    irc_write(&c_server, "NICK %s", cfg.awaynickname);
    }
}

void check_timers()
{
    FILE *fwd;

    if( i_client.connected ) {
        switch( proceed_timer( &c_client.timer, 60, 120 ) ) {
        case 0:
            break;
        case 1:
            irc_write( &c_client, "PING :%s", i_server.realname );
            break;
        case 2:
            drop_client( "Ping timeout" );
            error( CLNT_STONED );
            client_left();
            break;
        }
    }
    else {
        if( cfg.antiidle && ( proceed_timer( &timers.antiidle, 0, 600 ) == 2 ) ) irc_write( &c_server, "PRIVMSG" );
    }

    if( i_server.connected == 1 )
    {
        switch( proceed_timer( &c_server.timer, 60, 120 ) )
	{
	  case 0:
	    break;
	  case 1:
	    irc_write( &c_server, "PING :%s", i_server.realname );
	    break;
	  case 2:
	    drop_all( SERV_STONED );
	    error( SERV_STONED );
	    server_next( 0 );
	    break;
	}
    }

    if( i_server.connected == 2 ) {
        switch( proceed_timer( &c_server.timer, 90, 150 ) ) {
        case 0:
            break;
        case 1:
            irc_write( &c_server, "PING :%s", i_server.realname );
            break;
        case 2:
            drop_all( SERV_STONED );
            error( SERV_STONED );
            server_next( 0 );
            break;
        }
    }

    if( i_newclient.connected ) {
        switch( proceed_timer( &c_newclient.timer, 0, 20 ) ) {
        case 0:
        case 1:
            break;
        case 2:
            if( status.init ) {
                error( CLNT_AUTHFAIL );
                irc_write( &c_newclient, ":%s 464 %s :Password Incorrect", i_server.realname, cfg.nickname );
                drop_newclient( "Bad Password" );
            }
            else {
            	error( CLNT_AUTHTO );
                drop_newclient( "Ping timeout" );
            }
            if( i_client.connected ) irc_notice( &c_client, status.nickname, CLNT_AUTHFAILNOTICE, i_newclient.hostname );
            FREE( i_newclient.nickname );
            FREE( i_newclient.username );
            FREE( i_newclient.hostname );
            /* deallocate would also happen on next newclient-connect, but let's do it here */
            break;
        }
    }

    if( proceed_timer( &timers.listen, 0, 15 ) == 2 ) status.allowconnect = 1;

    if( proceed_timer( &timers.reply, 0, 4 ) == 2 ) status.allowreply = 1;

    if( cfg.getnick && !status.got_nick && !i_client.connected && ( proceed_timer( &timers.nickname, 0, 3 ) == 2 ) )
        irc_write( &c_server, "NICK %s", cfg.nickname );

    if( cfg.forwardmsg ) {
        switch( proceed_timer( &timers.forward, 0, 180 ) ) {
        case 0:
        case 1:
            break;
        case 2:
            if( forwardmsg && ( fwd = popen( cfg.forwardmsg, "w" ) ) ) {
                fprintf( fwd, "%s", forwardmsg );
                pclose( fwd );
                FREE( forwardmsg );
            }
            break;
        }
    }

    if( cfg.dccbounce )
	dcc_timer();
}


void server_reply_num( int command, char *origin, char *param1, char *param2, int *pass )
{
    char *chns;

    switch( command ) {
    case RPL_WELCOME:
        /* reply 001 - server-welcome */
        i_server.connected++;

        FREE( i_server.realname );
        i_server.realname = strdup( origin );

        FREE( status.nickname );
        status.nickname = strdup( param1 );

        FREE( i_server.greeting[ 0 ] );
        i_server.greeting[ 0 ] = strdup( param2 );

        FREE( status.idhostname );
        if( strchr( param2, '!' ) )
            status.idhostname = strdup( strchr( param2, '!' ) + 1 );
        else
            status.idhostname = strdup("(null)");

        i_server.greeting[ 0 ][ lastpos( i_server.greeting[ 0 ], ' ' ) ] = 0;
        report( IRC_CONNECTED, i_server.realname );
        irc_write( &c_server, "MODE %s :%s", status.nickname, cfg.umodes );
        if (cfg.connectcmd)
            irc_write( &c_server, "%s", cfg.connectcmd );

	if(!status.startup) 
	{
	    if(cfg.channels)
	    {
		report( MUH_JOINING, cfg.channels );
		irc_write( &c_server, "JOIN %s", cfg.channels );
	    }
	    
	    time(&status.startup);
	}
	else if((cfg.rejoin == 1) && (chns = list_channels()))
	{
            report( MUH_REJOINING, chns );
            irc_write( &c_server, "JOIN %s", chns );
	    drop_channels();
        }
	else if((cfg.rejoin == 2) && cfg.channels)
	{
	    report(MUH_REJOINING, cfg.channels);
	    irc_write(&c_server, "JOIN %s", cfg.channels);
	    drop_channels();
	}

	FREE( i_server.isupport[0] );
	FREE( i_server.isupport[1] );
	FREE( i_server.isupport[2] );

        break;

    case RPL_YOURHOST:
    case RPL_SERVERIS:
    case RPL_SERVERVER:
        /* your-host, your-server-is, server-version replies */
        FREE( i_server.greeting[ command - 1 ] );
        i_server.greeting[ command - 1 ] = strdup( param2 );

        break;

    case RPL_ISUPPORT:
	/* for loop? */
	if( !i_server.isupport[0] )
	    i_server.isupport[0] = strdup( param2 );
	else if( !i_server.isupport[1] )
	    i_server.isupport[1] = strdup( param2 );
	else if( !i_server.isupport[2] )
	    i_server.isupport[2] = strdup( param2 );
	break;

    case RPL_RESTRICTED:
        if( cfg.jumprestricted ) {
            drop_all( CLNT_RESTRICTED );
            report( SERV_RESTRICTED );
            server_next( 1 );
        }
        break;

    /* :<server> RPL_NOTOPIC <client> <channel> :No topic is set */
    case RPL_NOTOPIC:
        {
            struct channel *chptr;
            char *p;

            if((p = strchr(param2, ' ')) != NULL)
	        *p = '\0';
            else
                return;

            if((chptr = find_channel(param2)) != NULL)
                channel_topic(chptr, NULL);
        }

        break;

    /* :<server> RPL_TOPIC <client> <channel> :<topic> */
    case RPL_TOPIC:
        {
            struct channel *chptr;
            char *p;

            if((p = strchr(param2, ' ')) != NULL)
                *p++ = '\0';
            else
                return;

            if((chptr = find_channel(param2)) != NULL)
                channel_topic(chptr, p);
        }

	break;


    /* :<server> RPL_TOPICWHO <client> <channel> <who> <time> */
    case RPL_TOPICWHO:
        {
            struct channel *chptr;
            char *p, *topicwho;

	    if((p = strchr(param2, ' ')) != NULL)
	        *p++ = '\0';
  	    else
	        return;

	    topicwho = p;

	    if((p = strchr(topicwho, ' ')))
	        *p++ = '\0';
	    else
	        return;

            if((chptr = find_channel(param2)) != NULL)
                channel_when(chptr, topicwho, p);
        }

	break;

    default:
        /* let's ignore other replies for now */
        break;
    }

    if( !i_client.connected ) { /* falls kein client da */
        switch( command ) {
        case ERR_ERRONEUSNICKNAME:
            error( IRC_ERRIN, cfg.nickname );
            escape();
            break;

        case ERR_NICKUNAVAILABLE:
        case ERR_NICKNAMEINUSE:
            if( status.got_nick || ( i_server.connected != 2 ) ) {
                if( status.nickname && xstrcmp( status.nickname, cfg.altnickname ) == 0 ) { /* altnick doesn't work as well */
                    FREE( status.nickname );
                    status.nickname = ( char * )xmalloc( 9 );
                    randname( status.nickname, 8 );
                }
                else {
                    FREE( status.nickname );
                    status.nickname = strdup( cfg.altnickname );
                }

                if( command == ERR_NICKNAMEINUSE )
                    report( IRC_NICKINUSE, cfg.nickname, status.nickname );
                else
                    report( IRC_NICKUNAVAIL, cfg.nickname, status.nickname );
                irc_write( &c_server, "NICK %s", status.nickname );
            }
            status.got_nick = 0;
            break;

        default:
            break;
        }
    }
}

void server_reply_str( char *command, char *origin, char *param1, char *param2, int *pass )
{
    struct channel *chptr;
    char *nick, *hostname, *p;
    int i, l;
    int cmdindex;

    if((p = strchr(origin, '!')))
    {
	*p++ = '\0';
	nick = strdup(origin);
	hostname = strdup(p);
    }
    else
    {
        nick = strdup(origin);
        hostname = strdup(origin);
    }

    cmdindex = find_command(command);
    switch(cmdindex)
    {
	/* a command we dont know exists.. */
	case CMD_NONE:
	    break;

	case CMD_NICK:
            if(xstrcasecmp(status.nickname, nick) == 0)
	    {
                /* is that us who changed nick? */
                FREE(status.nickname);
                status.nickname = strdup(param1 + 1);

                if( xstrcasecmp(status.nickname, cfg.nickname) == 0)
	        {
                    status.got_nick = 1;
                    report(MUH_GOTNICK, status.nickname);
                }
                else
	            status.got_nick = 0;
            }

	    write_logentry_all(LOG_NICKS, LOGM_NICK,
			       gettimestamp2(), nick, param1 + 1);

	    break;

	case CMD_PONG:
	    *pass = 0;
	    break;

	case CMD_KICK:
            if((chptr = find_channel(param1)) == NULL)
               break;

            if(HAS_LOG(chptr, LOG_EXITS))
            {
                char *s;

                /* ugly, but done because we cant break up param2 */
                 if((s = strchr(param2, ' ')))
                 {
                     char *target;

                     *s = '\0';
                     target = strdup(param2);
                     *s = ' ';

                     write_logentry(chptr, LOGM_KICK,
                                    gettimestamp2(), target, nick, 
                                    nextword(param2) + 1);
                     FREE(target);
		}
	    }

	    if((xstrncmp(status.nickname, param2, pos(param2, ' ') - 1) == 0))
	    {
		if(!i_client.connected)
		    report(CLNT_KICK, origin, param1, nextword(param2) + 1);

		rem_channel(chptr);
		break;
	    }

	    break;

	case CMD_JOIN:
	    if(xstrcasecmp(status.nickname, nick) == 0)
		add_channel(param1 + 1);

            if((chptr = find_channel(param1 + 1)) == NULL)
                break;

	    if(HAS_LOG(chptr, LOG_JOINS))
		write_logentry(chptr, LOGM_JOIN,
		 	       gettimestamp2(), nick, hostname, param1 + 1);

	    break;

	case CMD_PART:
            if((chptr = find_channel(param1)) == NULL)
                break;
            
	    if(HAS_LOG(chptr, LOG_QUITS))
		write_logentry(chptr, LOGM_PART,
			       gettimestamp2(), nick, param1,
			       (param2) ? (param2 + 1) ? param2 + 1 : "" : "");

	    if(xstrcasecmp(status.nickname, nick) == 0)
	        rem_channel(chptr);

	    break;

	case CMD_QUIT:
	    write_logentry_all(LOG_QUITS, LOGM_QUIT,
			       gettimestamp2(), nick, param1 + 1, param2);

	    break;

	case CMD_KILL:
	    if(xstrcasecmp(status.nickname, nick) == 0)
		error(IRC_KILL, nick);

	    break;

	case CMD_MODE:
	    if((chptr = find_channel(param1)) == NULL)
                break;

            if(HAS_LOG(chptr, LOG_MODES))
		write_logentry(chptr, LOGM_MODES,
			       gettimestamp2(), nick, param2);

	    break;

        /* :<source> TOPIC <channel> :<topic> */
	case CMD_TOPIC:
            if((chptr = find_channel(param1)) == NULL)
                break;

            {
	        char timebuffer[20];
                struct tm *tmptr;
                time_t now;

                channel_topic(chptr, param2);

                time(&now);
                tmptr = gmtime(&now);
                strftime(timebuffer, 20, "%s", tmptr);
                channel_when(chptr, origin, timebuffer);
            }

	    if(HAS_LOG(chptr, LOG_MISC))
	        write_logentry(chptr, LOGM_TOPIC,
		 	       gettimestamp2(), nick, (param2 + 1) ? param2 + 1 : "");

	    break;

	case CMD_NOTICE:
	case CMD_PRIVMSG:
	    if(status.nickname && xstrcasecmp(param1, status.nickname) == 0)
	    {
	        if(!i_client.connected && is_perm(&peoplelist, origin))
	        {
	            /* CTCP */
	            if(param2[1] == '\1')
	   	    {
		        upcase(param2);

		        if((cmdindex == CMD_PRIVMSG) && cfg.dccbounce &&
                           (xstrcmp(param2 + 2, "DCC\1") == 0))
		        {
		            if(dcc_initiate(param2 + 1, 0))
			    {
			        irc_write(&c_client, ":%s PRIVMSG %s :%s", origin, param1, param2 + 1);
			        *pass = 0;
			    }
	  	        }
		        else if(!is_ignore(hostname, IGNORE_CTCP) && status.allowreply)
		        {
		            report(CLNT_CTCP, param2 + 1, origin);

			    if(xstrncmp(param2 + 2, "PING", 4) == 0)
			    {
			        if(strlen(param2 + 1) > 6)
			            irc_notice(&c_server, nick, "%s", param2 + 1);
			    }

			    else if(xstrcmp(param2 + 2, "VERSION\1") == 0)
			        irc_notice(&c_server, nick, VERSIONREPLY);

			    else if(xstrcmp(param2 + 2, "TIME\1") == 0)
			    {
			        time_t now;
			        char timebuffer[120];
			        struct tm *tmptr;

			        time(&now);
			        tmptr = localtime(&now);
			        strftime(timebuffer, 120, "%a %b %d %T %Y", tmptr);

			        irc_notice(&c_server, nick, TIMEREPLY, timebuffer);
			    }

			    /* dont bother sending USERINFO/CLIENTINFO/FINGER -- fl_ */
                            if( xstrcmp( param2 + 2, "USERINFO\1" ) == 0 )
	                        irc_notice( &c_server, nick, USERINFOREPLY );
          	            if( xstrcmp( param2 + 2, "CLIENTINFO\1" ) == 0 )
                  	        irc_notice( &c_server, nick, CLIENTINFOREPLY );
	                    if( xstrcmp( param2 + 2, "FINGER\1" ) == 0 )
        	                irc_notice( &c_server, nick, FINGERREPLY );

                            add_ignore(hostname, 6, IGNORE_CTCP);
	                    status.allowreply = 0;
        	            timers.reply = 0;
		        }
                        else
	                    report( CLNT_CTCPNOREPLY, param2 + 1, origin );
                    }

	            /* normal PRIVMSG/NOTICE to client */
		    else
		    {
		        if( !is_ignore( hostname, IGNORE_MESSAGE ) && status.allowreply )
		        {
                   	    if( cfg.awaynotice )
			        irc_notice( &c_server, nick, "%s", cfg.awaynotice );

                            add_ignore( hostname, 120, IGNORE_MESSAGE );
                            status.allowreply = 0;
                            timers.reply = 0;
                        }

                        if( cfg.logging && messagelog )
                        {
                            fprintf( messagelog, "%s(%s) %s\n", gettimestamp(), origin, param2 + 1 );
                            fflush( messagelog );
                        }

                        if( cfg.forwardmsg )
                        {
                            timers.forward = 0;
                            l = ( forwardmsg ? strlen( forwardmsg ) : 0 );
                            i = l + strlen( origin ) + strlen( param2 + 1 ) + 5;
                            forwardmsg = ( char * )xrealloc( forwardmsg, i );
                            sprintf( forwardmsg + l, "(%s) %s\n", origin, param2 + 1 );
		        }
                    }
		}
	    }
            /* privmsg to channel */
	    else
	    {
		int chw = 0;

		/* channel wallops - notice @#channel etc :) */
		if((param1[0] == '@') || (param1[0] == '%') || (param1[0] == '+'))
		{
		    chw = 1;
		    param1++;
		}

                if((chptr = find_channel(param1)) == NULL)
                    break;

		if(HAS_LOG(chptr, LOG_MESSAGES))
		{
                    if(chw)
                        param1--;

		    if(cmdindex == CMD_PRIVMSG)
		        write_logentry(chptr, LOGM_PRIVMSG,
				       gettimestamp2(), nick, param2 + 1);
		    else
			write_logentry(chptr, LOGM_NOTICE,
				       gettimestamp2, nick, param1, param2 + 1);
		}
            }

	    break;

	default:
	    break;
    }

    FREE( nick );
    FREE( hostname );
}

void server_commands( char *command, char *param, int *pass )
{
    upcase( command );

    if( xstrcmp( command, "PING" ) == 0 )
    {
        *pass = 0;
        if( param && param[ 0 ] == ':' ) param++;
        /* don't make this global (see ERROR) */
        if( param ) irc_write( &c_server, "PONG :%s", param );
    }

    if( xstrcmp( command, "ERROR" ) == 0 ) {
        *pass = 0;

        drop_server( NULL );
        drop_newclient( NULL );
        if( param )
            drop_client( param );
        else
            drop_client( SERV_ERR );

        if( param )
            error( IRC_SERVERERROR, param );
        else
            error( IRC_SERVERERROR, "unknown" );
        server_next( ( i_server.connected == 0 ) );
    }
}


int read_server()
{
    char *backup = 0;
    char *origin, *command, *param1, *param2;
    int rstate;
    int pass = 0;

    rstate = irc_read( &c_server );
    if( rstate > 0 ) { /* new data...go for it! */
        rstate = 0;
        if( strlen( c_server.buffer ) ) {
            pass = 1;

            backup = strdup( c_server.buffer );

            if( c_server.buffer[ 0 ] == ':' ) { /* reply */
                origin = strtok( c_server.buffer + 1, " " );
                command = strtok( NULL, " " );
                param1 = strtok( NULL, " " );
                param2 = strtok( NULL, "\0" );
#ifdef DEBUG
                printf( "[%s] [%s] [%s] [%s]\n", origin, command, param1, param2 );
#endif
                if( command ) {
                    server_reply_num( atoi( command ), origin, param1, param2, &pass );
                    server_reply_str( command, origin, param1, param2, &pass );
                }
            }
            else { /* command */
                command = strtok( c_server.buffer, " " );
                param1 = strtok( NULL, "\0" );

                if( command )
                    server_commands( command, param1, &pass );
            }

            if( i_client.connected && pass ) irc_write( &c_client, "%s", backup );
            FREE( backup );
        }
    }
    return rstate;
}


void fakeconnect()
{
    int i;
    time_t t;
    struct tm *tt;
    int pic = 0;

    irc_write( &c_client, ":%s 001 %s %s %s!~%s@%s", i_server.realname, status.nickname, i_server.greeting[ 0 ], status.nickname, i_client.username, i_client.hostname );
    for( i = 1; i < 4; i++ )
        irc_write( &c_client, ":%s %03d %s %s", i_server.realname, i + 1, status.nickname, i_server.greeting[ i ] );

    for( i = 0; i < 3; i++ )
    {
	if( i_server.isupport[i] )
	    irc_write( &c_client, ":%s 005 %s %s", i_server.realname, status.nickname, i_server.isupport[i] );
    }

    /* unset away */
    if (cfg.awayreason)
	irc_write( &c_server, ":%s AWAY", status.nickname );
    /* switch to online-nick */
    if (cfg.awaynickname)
	irc_write( &c_server, "NICK %s", cfg.nickname );
    irc_write( &c_server, "LUSERS" );

    if( !cfg.leave ) report( MUH_REINTRODUCE );

    /* das kann man deswegen immer senden, da (falls muh brav aus allen channels gegangen ist) es eh keinen channel
     * reply im whois gibt (mach ich wegen rehashs - damit alles klappt falls cfg.leave umgestellt wird)
     */

    irc_write( &c_client, ":%s 375 %s :- muh version "VERSION" -", i_server.realname, status.nickname );

    /* don't rely on extern int daylight */
    time( &t );
    tt = localtime( &t );

    pic = ( tt->tm_hour > 6 && tt->tm_hour < 19 ) ? 0 : 1;
    /* cows get up at six and go to sleep at seven :) */

    if( tt->tm_mday == 24 && tt->tm_mon == 11 ) pic = 2; /* xmas! (tm_mon is from 0..11) */

    for( i = 0; i < PIC_Y; i++ )
        irc_write( &c_client, ":%s 372 %s :%s", i_server.realname, status.nickname, pics[ pic ][ i ] );

    irc_write( &c_client, ":%s 372 %s :- running on server %s with nickname %s", i_server.realname, status.nickname, servers.data[ i_server.current ]->name, status.nickname  );

    if( messagelog && ftell( messagelog ) )
        irc_write( &c_client, ":%s 372 %s :- "CLNT_MESSAGES, i_server.realname, status.nickname );
    else
        irc_write( &c_client, ":%s 372 %s :- "CLNT_NOMESSAGES, i_server.realname, status.nickname );

    irc_write( &c_client, ":%s 376 %s :End of /MOTD command.", i_server.realname, status.nickname );

    if( xstrcmp( i_client.nickname, status.nickname ) != 0 ) {
        irc_write( &c_client, ":%s NICK :%s", i_client.nickname, status.nickname );
        FREE( i_client.nickname );
        i_client.nickname = strdup( status.nickname );
    }

    if( cfg.leave && cfg.channels && (channel_list.head != NULL))
    {
        report( MUH_REJOINING, cfg.channels );
	irc_write( &c_server, "JOIN %s", cfg.channels );
    }
    else if(channel_list.head != NULL)
    {
        dlink_node *ptr;
        struct channel *chptr;

	for(ptr = channel_list.head; ptr; ptr = ptr->next)
	{
            chptr = ptr->data;

	    irc_write(&c_client, ":%s!%s JOIN :%s",
		      status.nickname, status.idhostname,
		      chptr->name);

            if(chptr->topic != NULL)
            {
                irc_write(&c_client, ":%s %d %s %s %s",
		          i_server.realname, RPL_TOPIC, status.nickname,
		          chptr->name, chptr->topic);

                    if((chptr->topicwho != NULL) && (chptr->topicwhen != NULL))
		        irc_write(&c_client, ":%s %d %s %s %s %s",
		                  i_server.realname, RPL_TOPICWHO, status.nickname,
			          chptr->name, chptr->topicwho, chptr->topicwhen);
            }
	    else
	    {
		irc_write(&c_client, ":%s %d %s %s :No topic is set",
		          i_server.realname, RPL_NOTOPIC, status.nickname,
			  chptr->name);
            }

            if(HAS_LOG(chptr, LOG_MUHCLIENT))
                write_logentry(chptr, LOGM_MUH, gettimestamp2(), "");

            irc_write(&c_server, "NAMES %s", chptr->name);
	}
    }
}

int read_newclient()
{
    char *command, *param;
    int c_status = irc_read( &c_newclient );

    if(c_status > 0)
    {
        c_status = 0;
        c_newclient.buffer[ 30 ] = 0;
        command = strtok( c_newclient.buffer, " " );
        param = strtok( NULL, "\0" );

        if( command && param ) {
            upcase( command );
	    if( ( xstrcmp( command, "PASS" ) == 0 ) && !( status.init & 1 ) ) {
		/* only accept password once */
		if( *param == ':' ) param++;
                if( strlen( cfg.password ) == 13 || strlen( cfg.password ) == 28) { /* assume it's crypted */
                    if( xstrcmp( crypt( param, cfg.password ), cfg.password ) == 0 )
                        status.passok = 1;
                }
                else {
                    if( xstrcmp( param, cfg.password ) == 0 )
                        status.passok = 1;
                }
                status.init = status.init | 1;
            }
            if( xstrcmp( command, "NICK" ) == 0 ) {
		status.init = status.init | 2;
		FREE( i_newclient.nickname );
		i_newclient.nickname = strdup( strtok( param, " " ) );
            }

            if( xstrcmp( command, "USER" ) == 0 ) {
		status.init = status.init | 4;
		FREE( i_newclient.username );
		i_newclient.username = strdup( strtok( param, " " ) );
            }

            if( status.init == 7 && status.passok ) {  /* client ist da! */
                report( CLNT_AUTHOK );

                if( i_client.connected ) {
                    drop_client( CLNT_NEWCLIENT );
                    report( CLNT_DROP );
                }

                FREE( i_client.nickname );
                FREE( i_client.username );
                FREE( i_client.hostname );

                i_client.nickname = i_newclient.nickname;
                i_client.username = i_newclient.username;
                i_client.hostname = i_newclient.hostname;

                i_newclient.nickname = NULL;
                i_newclient.username = NULL;
                i_newclient.hostname = NULL;

                i_client.connected = 1;
                i_newclient.connected = 0;

                c_client.socket = c_newclient.socket;
                c_newclient.socket = 0;

                status.passok = 0;
                status.init = 0;
                fakeconnect();
            }
        }
        /* falls pass nicht ok wird einfach ausgetimed */
    }
    return c_status;
}

void muh_commands( char *command, char *param )
{
    int corr = 0;
    int i;
    char *s;

    if( !command )
    {
        irc_notice( &c_client, status.nickname, CLNT_COMANDS );
        return;
    }

    upcase( command );

    if( xstrcmp( command, "READ" ) == 0 ) {
        corr++;
        if( messagelog && ftell( messagelog ) ) {
            fflush( messagelog );
            rewind( messagelog );

            irc_notice( &c_client, status.nickname, CLNT_MSGLOGSTART );

            s = ( char * )xmalloc( 1024 );
            while( fgets( s, 1023, messagelog ) ) {
                if( s[ strlen( s ) - 1 ] == '\n' ) s[ strlen( s ) - 1 ] = 0;
                irc_notice( &c_client, status.nickname, "%s", s );
            }
            FREE( s );

            irc_notice( &c_client, status.nickname, CLNT_MSGLOGEND );
            fseek( messagelog, 0, SEEK_END );
        }
        else irc_notice( &c_client, status.nickname, CLNT_HAVENOMSGS );
    }

    else if(xstrcmp(command, "DEL") == 0)
    {
        corr++;
        if( messagelog ) {
            fclose( messagelog );
        }
        unlink( FILE_MESSAGES );
        if( cfg.logging )
            messagelog = fopen( FILE_MESSAGES, "w+" );

        irc_notice( &c_client, status.nickname, CLNT_KILLEDMSGS );
    }

    else if( xstrcmp( command, "REHASH" ) == 0 )
    {
        corr++;
        irc_notice( &c_client, status.nickname, MUH_REHASH );
        rehash();
    }

    else if(xstrcmp(command, "RESET") == 0)
    {
	corr++;
	irc_notice(&c_client, status.nickname, MUH_RESET);
	server_reset();
    }

    else if(xstrcmp(command, "UPTIME") == 0)
    {
	time_t now;
	int seconds, minutes, hours, days;

	corr++;
	time(&now);
	now -= status.startup;
        getuptime(now, &days, &hours, &minutes, &seconds),

	irc_notice(&c_client, status.nickname,
		   MUH_UPTIME, days, hours, minutes, seconds);
    }

    else if( xstrcmp( command, "JUMP" ) == 0 )
    {
        corr++;
        drop_all( MUH_JUMP );
        report( MUH_JUMP"\n" );
        if( param ) {
            i = atoi( param );
            i--;
            if( i < 0 ) i = 0;
            if( i >= servers.amount ) i = servers.amount - 1;
            servers.data[ i ]->working = 1;
            i_server.current = i - 1;
        }
        server_next( 0 );
    }

    else if( xstrcmp( command, "DIE" ) == 0 ) {
        corr++;
        drop_all( MUH_DIE_CL );
        report( MUH_DIE );
        escape();
    }

    else if( xstrcmp( command, "PRINT" ) == 0 ) {
        corr++;
        irc_notice( &c_client, status.nickname, CLNT_SLIST );
        for( i = 0; i < servers.amount; i++ ) {
            irc_notice( &c_client, status.nickname, "%c[%d] %s:%d%s",
                        ( servers.data[ i ]->working ? '+' : '-' ),
                        i + 1,
                        servers.data[ i ]->name,
                        servers.data[ i ]->port,
                        ( servers.data[ i ]->password ? ":*" : "" ) );
        }
        irc_notice( &c_client, status.nickname, CLNT_CURRENT, i_server.current + 1 );
    }

    if( !corr ) irc_notice( &c_client, status.nickname, CLNT_COMANDS );
}

int read_client()
{
    int c_status;
    char *backup, *command, *param1, *param2;
    int pass = 1;

    c_status = irc_read(&c_client);

    /* new data.. */
    if(c_status > 0)
    {
        c_status = 0;

        if( strlen( c_client.buffer ) )
	{
            backup = strdup( c_client.buffer );

            command = strtok( c_client.buffer, " " );
            param1 = strtok( NULL, " " );
            param2 = strtok( NULL, "\0" );
            if( param1 && param1[ 0 ] == ':' ) param1++;

            if( command )
	    {
                upcase( command );

                if( xstrcmp( command, "MUH" ) == 0 )
		{
                    muh_commands( param1, param2 );
                    pass = 0;
                }

		else if( xstrcmp( command, "QUIT" ) == 0 )
		{
                    drop_client( "muh!" );
                    client_left();
                    report( CLNT_LEFT );
                    pass = 0;
                }

		else if( xstrcmp( command, "PONG" ) == 0 )
		{
                    /* burp */
                    pass = 0;
                }

		else if( xstrcmp( command, "PING" ) == 0 )
		{
                    irc_write( &c_client, ":%s PONG %s :%s", i_server.realname, i_server.realname, status.nickname );
                    pass = 0;
                }

		else if(xstrcmp(command, "PRIVMSG") == 0)
		{
	            if(cfg.dccbounce && xstrncmp(param2, ":\1DCC", 5) == 0)
		    {
			if(dcc_initiate(param2 + 1, 1))
			{
			    irc_write(&c_server, "PRIVMSG %s %s", param1, param2);
			    pass = 0;
			}
		    }
		    else if((param2[0] != '\1') && (param1[0] == '#'))
		    {
			struct channel *chptr;

                        if((chptr = find_channel(param1)) != NULL)
                        {
			    if(HAS_LOG(chptr, LOG_MESSAGES))
			        write_logentry(chptr, LOGM_PRIVMSG,
					       gettimestamp2(), status.nickname, 
                                               param2 + 1);
                        }
		    }
		}
            }
            if( pass ) irc_write( &c_server, "%s", backup );
            FREE( backup );
        }
    }
    return c_status;
}

void run()
{
    fd_set rfds, wfds;
    struct timeval tv;
    int selret;

    while( 1 ) {
        if( !i_server.connected ) { /*schon wohin connected?*/
            report( SERV_TRYING, servers.data[ i_server.current ]->name, servers.data[ i_server.current ]->port );
            switch( irc_connect( &c_server, servers.data[ i_server.current ], cfg.nickname, cfg.username, cfg.realname, cfg.bind ) ) {
            case 0:
                report( SOCK_CONNECT, servers.data[ i_server.current ]->name );
                i_server.connected = 1;
                break;
            case 1:
                error( SOCK_ERROPEN );
                escape();
                break;
            case 2:
                error( SOCK_ERRRESOLVE, servers.data[ i_server.current ]->name );
                drop_server( NULL );
                server_next( 1 );
                break;
            case 3:
                if( cfg.bind )
                    error( SOCK_ERRBINDHOST, cfg.bind, cfg.listenport );
                else
                    error( SOCK_ERRBIND, cfg.listenport );
                escape();
                break;
            case 4:
                error( SOCK_ERRCONNECT, servers.data[ i_server.current ]->name, strerror( errno ) );
                drop_server( NULL );
                server_next( 1 );
                break;
            case 5:
                error( SOCK_ERRWRITE, servers.data[ i_server.current ]->name );
                drop_server( NULL );
                server_next( 0 );
                break;
            case 6:
                error( SOCK_GENERROR, net_errstr );
                escape();
                break;
            default:
                break;
            }
        }

        tv.tv_usec = 0;
        tv.tv_sec = 1;

        FD_ZERO( &rfds );
	FD_ZERO( &wfds );

        if( ( i_server.connected == 2 ) && status.allowconnect && ( !i_newclient.connected ) ) FD_SET( listensocket, &rfds );
        if( i_server.connected ) FD_SET( c_server.socket, &rfds );
        if( i_client.connected ) FD_SET( c_client.socket, &rfds );
        if( i_newclient.connected ) FD_SET( c_newclient.socket, &rfds );

	if(cfg.dccbounce)
	    dcc_socketsubscribe( &rfds, &wfds );
#ifdef DEBUG
        printf( "(highest is %d)\n", highest_socket );
#endif

        selret = select( highest_socket + 1, &rfds, &wfds, NULL, &tv );

        if( selret > 0 ) {
            if( FD_ISSET( c_server.socket, &rfds ) ) { /* der server will was */
                if( read_server() < 0 ) {
                    drop_all( SERV_DROPPED );
                    error( SERV_DROPPED );
                    server_next( 0 );
                }
            }

            if( FD_ISSET( listensocket, &rfds ) ) { /* ein neuer client! */
                status.allowconnect = 0;
                FREE( i_newclient.hostname );
                if( ( c_newclient.socket = sock_accept( listensocket, &i_newclient.hostname, 1) ) > 0 ) {
                    c_newclient.offset = 0;
                    i_newclient.connected = 1;
                    if( !i_client.connected )
                        report( CLNT_CAUGHT, i_newclient.hostname );
                    else {
                        report( CLNT_RECONNECT, i_newclient.hostname );
                    }
                }
                else {
                    if( c_newclient.socket ) /* denied */
                        report( CLNT_DENIED, i_newclient.hostname );
                    else /* error */
                        error( SOCK_ERRACCEPT, i_newclient.hostname );
                    FREE( i_newclient.hostname );
                    c_newclient.socket = 0;
                }
            }

            if( FD_ISSET( c_client.socket, &rfds ) ) { /* der client redet */
                if( read_client() < 0 ) {
                    /* client hat connection gedroppt */
                    drop_client( NULL );
                    client_left();
                    report( CLNT_DROPPED );
                }
            }

            if( FD_ISSET( c_newclient.socket, &rfds ) ) { /* der neue client sagt was */
                if( read_newclient() < 0 ) {
                    /* newclient hat connection gedroppt */
                    drop_newclient( NULL );
                    report( CLNT_DROPPEDUNAUTH );
                }
            }

	    if(cfg.dccbounce)
		dcc_socketcheck( &rfds, &wfds );
        }

        if( !selret ) { /* it was a timeout then (*every* second) */
            check_timers();
            process_ignores();
        }
    }
}

void init()
{
    struct sigaction sv;

    sigemptyset( &sv.sa_mask );
    sv.sa_flags = 0;
    sv.sa_handler = sig_term;
    sigaction( SIGTERM, &sv, NULL );
    sigaction( SIGINT, &sv, NULL );
    sigaction( SIGKILL, &sv, NULL );

    sv.sa_handler = rehash;
    sigaction( SIGHUP, &sv, NULL );

    sv.sa_handler = SIG_IGN;
    sigaction( SIGUSR1, &sv, NULL );
    sigaction( SIGPIPE, &sv, NULL );
    /* signalhandler hooken */

    umask( ~S_IRUSR & ~S_IWUSR );
    /* fuer logfile(s) */

    status.got_nick = 1; /* assume everythings fine */
    status.allowconnect = 1;
    status.startup = 0;
    i_server.current = 0; /* start with first server */

    srand( time( NULL ) );

    create_listen();

    if( !( messagelog = fopen( FILE_MESSAGES, "a+" ) ) ) {
        report( MUH_ERRMSGFILE );
    }
}

int checkconfig()
{
    int err = 0;
#define REPORTERROR(x) { error( PARSE_MK, x ); err++; }
    if( !cfg.listenport ) REPORTERROR( "listenport" );
    if( !cfg.password ) REPORTERROR( "password" );
    if( !cfg.nickname ) REPORTERROR( "nickname" );
    if( !cfg.altnickname ) REPORTERROR( "altnickname" );
    if( !cfg.username ) REPORTERROR( "username" );
    if( !cfg.realname ) REPORTERROR( "realname" );

    if(!cfg.listenhost)
    {
        if(cfg.bind)
	    cfg.listenhost = cfg.bind;
    }

    if(!servers.amount)
    {
        error(PARSE_NOSERV);
	err++;
    }

    return ( err == 0 );
}

void setup_home( char *s )
{
    if( s ) {
        cfg.home = strdup( s );
        if( cfg.home[ strlen( cfg.home ) - 1 ] != '/' ) {
            cfg.home = xrealloc( cfg.home, strlen( cfg.home ) + 2 );
            strcat( cfg.home, "/" );
        }
    }
    else {
        if( !( s = getenv( "HOME" ) ) ) {
            error( MUH_ERRNOHOME );
            escape();
        }

        cfg.home = xmalloc( strlen( s ) + strlen( MUHDIR ) + 2 );
        xstrcpy( cfg.home, s );

        if( cfg.home[ strlen( cfg.home ) - 1 ] != '/' ) {
            strcat( cfg.home, "/" );
        }
        strcat( cfg.home, MUHDIR );
    }

    if( chdir( cfg.home ) < 0 ) {
        error( MUH_ERRCHDIR, cfg.home );
        escape();
    }
}

int main( int paramc, char *params[] )
{
    int pid = 0;
    FILE *pidfile;
    char *muhdir = 0;
    int dofork = 1;
    int c;
    char salt[ 3 ];

    fprintf( stdout, "%s", BANNER );

    opterr = 0;

    while( ( c = getopt( paramc, params, ":cfd:" ) ) > 0 ) {
        switch( c ) {
        case 'c':
            srand( time( NULL ) );
            randname( salt, 2 );
            printf( MUH_THISPASS, crypt( getpass( MUH_ENTERPASS ), salt ) );
            return 0;
            break;
        case 'd':
            muhdir = optarg;
            break;
        case 'f':
            dofork = 0;
            break;
        case ':':
            error( MUH_ERRNEEDARG, optopt );
            escape();
            break;
        default:
            printf( SYNTAX, params[ 0 ] );
            return 1;
            break;
        }
    }

    setup_home( muhdir );

    read_cfg();
    if( !checkconfig() ) escape();

    setup_commands();

    init();

    if( dofork ) {
        pid = fork();
        if( pid < 0 ) {
            error( MUH_ERRFORK );
            escape();
        }
        if( pid == 0 ) {
            if( !freopen( FILE_LOG, "a", stdout ) ) {
                error( MUH_ERRFILE, cfg.home );
                escape();
            }
#ifndef SETVBUF_REVERSED
            setvbuf( stdout, NULL, _IONBF, 0 );
#else
            setvbuf( stdout, _IONBF, NULL, 0 );
#endif
            printf( "\n" );
            report( MUH_NEWSESSION );
            report( MUH_STARTINGLOG );
            if( cfg.listenhost )
                report( SOCK_LISTENOKHOST, cfg.listenhost, cfg.listenport );
            else
                report( SOCK_LISTENOK, cfg.listenport );
            report( MUH_NICK, cfg.nickname );

        }
        if( pid ) {
            if( !( pidfile = fopen( FILE_PID, "w" ) ) ) {
                error( MUH_ERRFILE, cfg.home );
                kill( pid, SIGTERM );
                escape();
            }
            fprintf( pidfile, "%d\n", pid );
            fclose( pidfile );
            report( MUH_NICK, cfg.nickname );
            report( MUH_FORKED, pid );
            exit( 0 );
        }
    }
    run();
    return 0;
}
