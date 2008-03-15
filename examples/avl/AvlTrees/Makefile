# <plaintext>
#######################################################
# Makefile for the AVL tree classes to put them in
# the library directory
#######################################################

CC = g++
CFLAGS = -g

TREE   = Avl
OBJS   = ${TREE}.o
TEST   = ${TREE}Test

all : ${OBJS}

test : ${TEST}
	${TEST}

clean :
	rm -f ${OBJS}

clobber : clean
	rm -f ${TARGET} ${TEST}

${TREE}.o : ${TREE}.cc ${TREE}.h Comparable.h TestVals.h
	${CC} ${CFLAGS} -c ${TREE}.cc
	
${TREE}Test : ${OBJS} ${TREE}.h ${TREE}Test.cc
	${CC} ${CFLAGS} -o $@ ${TEST}.cc ${OBJS}

