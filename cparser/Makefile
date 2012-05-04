OCAMLBUILD = ocamlbuild

# number of parallel jobs, 0 means unlimited.
JOBS = 0

# dynlink should precede camlp4lib
LIBS = unix,str,nums,dynlink,$(CURDIR)/../cil/cil-1.4.0/obj/x86_LINUX/cil
LIBS2 = unix,str,nums,$(CURDIR)/../cil/cil-1.4.0/obj/x86_LINUX/cil

INCLUDES = -I,$(CURDIR)/../cil/cil-1.4.0/obj/x86_LINUX,-I,+$(CURDIR)/../cil/cil-1.4.0/src,-I,+$(CURDIR)/../cil/cil-1.4.0/src/frontc

FLAGS = $(INCLUDES),-g,-annot

# -no-hygiene flag to disable "hygiene" rules
OB_FLAGS = -no-links -libs $(LIBS) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) 

OBG_FLAGS = -no-links -libs $(LIBS2) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) 

all: byte

native: cilhip.native

byte: cilhip.byte

cilhip.byte:
	@ocamlbuild cilhip.byte $(OB_FLAGS)
	cp -u _build/cilhip.byte cilhip
	cp -u _build/cilhip.byte b-cilhip

cilhip.native:
	@ocamlbuild cilhip.native $(OBG_FLAGS)
	cp -u _build/cilhip.native cilhip
	cp -u _build/cilhip.native n-cilhip

clean:
	@ocamlbuild -quiet -clean
	rm -f b-cilhip n-cilhip cilhip
	rm -f *.cmo *.cmi *.cmx *.o *.mli *.output *.annot

