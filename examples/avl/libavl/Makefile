## <plaintext>

######
## targets
######
LIBRARY=	libavl.a
TEST=	avl_test

######
## options
######
DBG=	-g
DEFS=	
#OPT=	-O
CFLAGS= $(DBG) $(OPT) $(DEFS) $(OPTIONS)

######
## files
######
MISCFILES=	DISCUSSION  LICENSE  MANIFEST  avl.3  key_gen.c  rotate.old
MAKEFILE=	Makefile
HDRS=	avl.h   avl_typs.h   testvals.h
OBJS=	avl.o   avl_test.o
SRCS=	avl.c \
		avl_test.c

######
## commands
######
COPY=	cp
DEL=	rm -f
PRINT=	pr

######
## directories
######
LOCAL=	/usr/local
INCDIR=	$(LOCAL)/include
LIBDIR=	$(LOCAL)/lib

######
## target dependencies
######
all: library test

library: $(LIBRARY)

test: $(TEST)

$(LIBRARY):	avl.o
	ar cru $(LIBRARY) avl.o
	ranlib $(LIBRARY)

$(TEST): $(OBJS)
	$(CC) $(CFLAGS) -o $(TEST) $(OBJS)

install: $(LIBRARY) avl.h
	$(COPY) avl.h $(INCDIR)/avl.h
	$(COPY) $(LIBRARY) $(LIBDIR)/$(LIBRARY)

clean:
	$(DEL) $(OBJS)

clobber: clean
	$(DEL) $(LIBRARY) $(TEST)
	
index:
	ctags -wx $(HDRS) $(SRCS)

print:
	$(PRINT) $(HDRS) $(SRCS)

tags: $(HDRS) $(SRCS)
	 ctags $(HDRS) $(SRCS)

man: avl.man

avl.man: avl.3
	nroff -man avl.3 | col -b >avl.man

######
## object dependencies
######
avl.o: avl.h avl_typs.h
avl_test.o: avl.h testvals.h

