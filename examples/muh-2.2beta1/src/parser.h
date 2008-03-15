#ifndef BISON_Y_TAB_H
# define BISON_Y_TAB_H

#ifndef YYSTYPE
typedef union {
	int boolean;
	int number;
	char * string;
} yystype;
# define YYSTYPE yystype
# define YYSTYPE_IS_TRIVIAL 1
#endif
# define	BOOLEAN	257
# define	NUMBER	258
# define	STRING	259
# define	NICKNAME	260
# define	REALNAME	261
# define	USERNAME	262
# define	SERVERS	263
# define	HOSTS	264
# define	PEOPLE	265
# define	LISTENPORT	266
# define	LISTENHOST	267
# define	PASSWORD	268
# define	ALTNICKNAME	269
# define	LOGGING	270
# define	LEAVE	271
# define	LEAVEMSG	272
# define	AWAY	273
# define	GETNICK	274
# define	BIND	275
# define	ANTIIDLE	276
# define	NEVERGIVEUP	277
# define	NORESTRICTED	278
# define	REJOIN	279
# define	FORWARDMSG	280
# define	CHANNELS	281
# define	DCCBOUNCE	282
# define	DCCBINDCLIENT	283
# define	LOG	284
# define	TYPE	285
# define	CHANNEL	286
# define	LOGFILE	287
# define	L_JOINS	288
# define	L_EXITS	289
# define	L_QUITS	290
# define	L_MODES	291
# define	L_MESSAGES	292
# define	L_NICKS	293
# define	L_MISC	294
# define	L_MUHCLIENT	295
# define	L_ALL	296


extern YYSTYPE yylval;

#endif /* not BISON_Y_TAB_H */
