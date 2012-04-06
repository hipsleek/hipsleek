OCAMLBUILD = ocamlbuild

# number of parallel jobs, 0 means unlimited.
JOBS = 0

# dynlink should precede camlp4lib
LIBS = unix,dynlink,camlp4lib
LIBS2 = unix,dynlink,camlp4lib

INCLUDES = -I,+camlp4,-I,+site-lib/batteries

FLAGS = $(INCLUDES),-g,-annot

# -no-hygiene flag to disable "hygiene" rules
OB_FLAGS = -no-links -libs $(LIBS) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) 

OBG_FLAGS = -no-links -libs $(LIBS2) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) 

XML = cd $(CURDIR)/xml; make all; make opt; cd ..

all: spb 
native: spn

spb:
	@ocamlbuild -verbose 10 $(OB_FLAGS) sp_main.byte
	cp -u _build/sp_main.byte sp_main
	cp -u _build/sp_main.byte b-sp_main

spn:
	@ocamlbuild -verbose 4 $(OB_FLAGS) sp_main.native
	cp -u _build/sp_main.native sp_main
	cp -u _build/sp_main.native n-sp_main

# Clean up
clean:
	$(OCAMLBUILD) -quiet -clean 
	rm -f sp_main n-sp_main b-sp_main
	rm -f *.cmo *.cmi *.cmx *.o *.mli *.output *.annot splexer.ml 

install:
	cp sp_main /usr/local/bin/sp_main
	