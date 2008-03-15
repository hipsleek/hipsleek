dnl $Id: configure.ac,v 1.1.1.1 2008-03-15 06:55:01 nguyenh2 Exp $

AC_INIT
AC_CONFIG_SRCDIR([src/muh.c])
AM_INIT_AUTOMAKE(muh, `cat ./${srcdir}/VERSION`)
AM_CONFIG_HEADER(config.h)

AC_ARG_ENABLE(local, AC_HELP_STRING([--enable-local],[install muh locally, not system-wide]), ac_local=yes, ac_local=no)
AC_ARG_ENABLE(ipv6, AC_HELP_STRING([--enable-ipv6],[enable ipv6-support]))

dnl Checks for programs.
AC_PROG_CC

AC_PROG_MAKE_SET
AC_PROG_INSTALL

AC_PROG_YACC
AM_PROG_LEX

if test "$ac_local" = yes; then
	AC_MSG_RESULT(configuring for local installation)
	bindir=$HOME/muh
	sbindir=$bindir
	datadir=$HOME/.muh
	infodir=$HOME/muh
	mandir=$infodir
fi
AC_SUBST(ac_local)

if test "$GCC" = yes; then
	CFLAGS="${CFLAGS} -Wall"
fi

AH_TEMPLATE([IPV6],[IPV6 available?])
if test "$enable_ipv6" = yes; then
	AC_CHECK_FUNC(gethostbyname2,AC_DEFINE(IPV6))
fi

dnl Checks for libraries.
AC_SEARCH_LIBS(gethostbyname,nsl)
AC_SEARCH_LIBS(gethostbyaddr,nsl)
AC_SEARCH_LIBS(socket,socket)
AC_SEARCH_LIBS(hstrerror,resolv)
AC_SEARCH_LIBS(crypt,crypt)

dnl Checks for header files.
AC_HEADER_STDC

if test "$ac_cv_header_stdc" = no; then
  AC_MSG_ERROR(ansi-c headers are required!)
fi

AC_CHECK_HEADERS(fcntl.h sys/time.h unistd.h errno.h pwd.h crypt.h)
AC_CHECK_HEADERS(sys/types.h sys/socket.h sys/stat.h netinet/in.h netdb.h arpa/inet.h signal.h ctype.h strings.h)

dnl Checks for typedefs, structures, and compiler characteristics.
AC_C_CONST
AC_TYPE_SIZE_T
AC_HEADER_TIME
AC_STRUCT_TM


dnl Checks for library functions.
AC_FUNC_ALLOCA
AC_FUNC_SETVBUF_REVERSED
AC_TYPE_SIGNAL
AC_FUNC_STRFTIME
AC_CHECK_FUNCS(select socket gethostbyname gethostbyaddr strerror strdup sigemptyset,,AC_MSG_ERROR(required function not found))
AC_CHECK_FUNCS(strncasecmp strcasecmp vsnprintf bzero crypt getpass gethostname,,AC_MSG_ERROR(required function not found))
AC_CHECK_FUNCS(sigaction random hstrerror)

AC_CHECK_FUNCS(backtrace backtrace_symbols)

AC_CONFIG_FILES([Makefile src/Makefile doc/Makefile misc/Makefile misc/muhrc muh.spec])
AC_OUTPUT

AC_MSG_RESULT(now type 'make' to compile)

