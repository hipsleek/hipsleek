OCAMLBUILD = ocamlbuild

#  number of parallel jobs, 0 means unlimited.
JOBS = 0

# dynlink should precede camlp4lib
LIBSB = unix,str,graph,dynlink,camlp4lib,nums,site-lib/batteries/batteries,site-lib/extlib/extLib
LIBSN = unix,str,graph,dynlink,camlp4lib,nums,site-lib/batteries/batteries,site-lib/extlib/extLib
#,z3
LIBS2 = unix,str,graph,lablgtk,lablgtksourceview2,dynlink,camlp4lib

INCLUDES = -I,+ocamlgraph,-I,+lablgtk2,-I,+camlp4,-I,+site-lib/batteries,-I,+site-lib/extlib

FLAGS = $(INCLUDES),-g,-annot,-ccopt,-fopenmp 
# ,-cclib,-lz3stubs,-cclib,-lz3,/usr/local/lib/ocaml/libcamlidl.a

# -no-hygiene flag to disable "hygiene" rules
OBB_FLAGS = -no-links -libs $(LIBSB) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) 
OBN_FLAGS = -no-links -libs $(LIBSN) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) 

OBG_FLAGS = -no-links -libs $(LIBS2) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) 

all: byte 

byte: runz3.byte 
native: runz3.native 
runz3: runz3.native
	
runz3.byte: 
	@ocamlbuild $(OBB_FLAGS) main.byte
	cp -u _build/main.byte runz3
	cp -u _build/main.byte b-runz3

runz3.native: 
	@ocamlbuild $(OBN_FLAGS) main.native
	cp -u _build/main.native runz3
	cp -u _build/main.native n-runz3


# Clean up
clean:
	$(OCAMLBUILD) -quiet -clean 
	rm -f runz3 runz3.norm runz3.byte b-runz3 n-runz3
	rm -f *.cmo *.cmi *.cmx *.o *.mli *.output *.annot 


