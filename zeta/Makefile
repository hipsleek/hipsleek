OCAMLBUILD = ocamlbuild

OCAMLLIB=/usr/lib/ocaml

# number of parallel jobs, 0 means unlimited.
JOBS = 0

# dynlink should precede camlp4lib
LIBS = unix,str,dynlink,camlp4lib,z3
LIBS2 = unix,str,dynlink,camlp4lib,z3
INCLUDES = -I,+camlp4,-I,$(CURDIR)/z3
FLAGS = $(INCLUDES),-g,-annot,-ccopt,"-fopenmp",-cclib,-lz3,-cclib,-lz3stubs,$(OCAMLLIB)/libcamlidl.a,-I,$(CURDIR)/z3

# -no-hygiene flag to disable "hygiene" rules
OB_FLAGS = -no-links -pp "camlp4o pa_extend.cmo" -libs $(LIBS) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) 

all: zeta

zeta:
	@ocamlbuild $(OB_FLAGS) zmain.native
	cp -u _build/zmain.native zeta

clean:
	$(OCAMLBUILD) -quiet -clean 
	rm -f zeta
	rm -f zeta2

zetatwo:
	@ocamlbuild $(OB_FLAGS) zeta.native
	cp -u _build/zeta.native zeta2
