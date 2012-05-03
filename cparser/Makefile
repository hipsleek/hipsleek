OCAMLBUILD = ocamlbuild

# number of parallel jobs, 0 means unlimited.
JOBS = 0

# dynlink should precede camlp4lib
LIBS = unix,str,nums,$(CURDIR)/../cil/cil-1.4.0/obj/x86_LINUX/cil
LIBS2 = unix,str,nums

INCLUDES = -I,$(CURDIR)/../cil/cil-1.4.0/obj/x86_LINUX,-I,+$(CURDIR)/../cil/cil-1.4.0/src,-I,+$(CURDIR)/../cil/cil-1.4.0/src/frontc

FLAGS = $(INCLUDES),-g,-annot

# -no-hygiene flag to disable "hygiene" rules
OB_FLAGS = -no-links -libs $(LIBS) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) 

OBG_FLAGS = -no-links -libs $(LIBS2) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) 

all:cilhip

cilhip:
	@ocamlbuild cilhip.native $(OB_FLAGS)
	cp -u _build/cilhip.native cilhip
	cp -u _build/cilhip.native b-cilhip
