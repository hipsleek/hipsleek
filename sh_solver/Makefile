OCAMLBUILD = ocamlbuild

# number of parallel jobs, 0 means unlimited.
JOBS = 0

LIBS = unix,str,nums,site-lib/batteries/batteries,z3
INCLUDES = -I,+site-lib/batteries
#-cclib -lz3stubs -cclib -lz3 /usr/local/lib/ocaml/libcamlidl.a

FLAGS = $(INCLUDES),-g,-annot
LFLAGS = $(FLAGS),-ccopt,-fopenmp,-cclib,-lz3stubs,-cclib,-lz3,/usr/local/lib/ocaml/libcamlidl.a

# -no-hygiene flag to disable "hygiene" rules
OB_FLAGS = -no-links  -libs $(LIBS) -cflags $(FLAGS) -lflags $(LFLAGS) -lexflag -q -yaccflag -v
all: spn


#byte: spb
#spb:
#	@ocamlbuild $(OB_FLAGS) sp_main.byte
#	cp -u _build/sp_main.byte sp_main
#	cp -u _build/sp_main.byte b-sp_main

spn:
	@ocamlbuild $(OB_FLAGS) sp_main.native
	cp -u _build/sp_main.native sp_main
	cp -u _build/sp_main.native n-sp_main

# Clean up
clean:
	$(OCAMLBUILD) -quiet -clean 
	rm -f sp_main n-sp_main b-sp_main
	rm -f *.cmo *.cmi *.cmx *.o *.mli *.output *.annot splexer.ml 

install:
	cp sp_main /usr/local/bin/sp_main
	