OCAMLBUILD = ocamlbuild
MINISATDIR2=/home/bachle/fixed_ocamlminisat14
EXDIROFSLK=/home/bachle/slicing_minisat/sleekex

# number of parallel jobs, 0 means unlimited.
JOBS = 0

# dynlink should precede camlp4lib
LIBS = unix,threads,str,graph,xml-light,dynlink,camlp4lib
LIBS2 = unix,threads,str,graph,xml-light,lablgtk,lablgtksourceview2,dynlink,camlp4lib,$(MINISATDIR2)/MiniSAT

INCLUDES = -I,+ocamlgraph,-I,$(MINISATDIR2),-I,$(CURDIR)/xml,-I,+lablgtk2,-I,+camlp4,-I,-cclib

FLAGS = $(INCLUDES),-g,-annot

# -no-hygiene flag to disable "hygiene" rules
OB_FLAGS = -no-links -no-hygiene -libs $(LIBS) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) 

OBG_FLAGS = -no-links -no-hygiene -libs $(LIBS2) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) 

XML = cd $(CURDIR)/xml; make all; make opt; cd ..
MNS = cd $(MINISATDIR2); make all; cp $(MINISATDIR2)/Solver.o $(EXDIROFSLK); cp $(MINISATDIR2)/MiniSATWrap.o $(EXDIROFSLK); cd $(EXDIROFSLK) ; pwd
all: byte decidez.vo 

#--------------

#--------------
#gui
byte: sleek.byte hip.byte
native: hip.native sleek.native
gui: ghip.native gsleek.native
byte-gui: ghip.byte gsleek.byte

hip: hip.native
sleek: sleek.native
ghip: ghip.native
gsleek: gsleek.native

xml: xml/xml-light.cma

xml/xml-light.cma:
	$(XML)

mns: $(MINISATDIR2)/MiniSAT.cma

$(MINISATDIR2)/MiniSAT.cma:
	$(MNS)

hip.byte: xml mns
	@ocamlbuild $(OB_FLAGS) main.byte
	cp -u _build/main.byte hip
	cp -u _build/main.byte b-hip

hip.native: xml mns
	@ocamlbuild $(OB_FLAGS) main.native
	cp -u _build/main.native hip
	cp -u _build/main.native n-hip

sleek.byte: xml mns
	@ocamlbuild $(OB_FLAGS) sleek.byte
	cp -u _build/sleek.byte sleek
	cp -u _build/sleek.byte b-sleek

sleek.native: xml mns
	@ocamlbuild $(OB_FLAGS) sleek.native
	cp -u _build/sleek.native sleek
	cp -u _build/sleek.native n-sleek

gsleek.byte: 
	@ocamlbuild $(OBG_FLAGS) gsleek.byte
	cp -u _build/gsleek.byte p-gsleek

gsleek.native: 
	@ocamlbuild $(OBG_FLAGS) gsleek.native
	cp -u _build/gsleek.native gsleek

ghip.byte:
	@ocamlbuild $(OBG_FLAGS) ghip.byte
	cp -u _build/ghip.byte p-ghip

ghip.native:
	@ocamlbuild $(OBG_FLAGS) ghip.native
	cp -u _build/ghip.native ghip

# Clean up
clean:
	$(OCAMLBUILD) -quiet -clean 
	rm -f sleek sleek.norm hip hip.norm gsleek ghip sleek.byte hip.byte
	rm -f *.cmo *.cmi *.cmx *.o *.mli *.output *.annot slexer.ml ilexer.ml lexer.ml iparser.ml oclexer.ml ocparser.ml rlparser.ml rllexer.ml
#	rm -f iparser.mli iparser.ml iparser.output oc.out

decidez.vo:
	coqtop -compile decidez

install:
	cp mona_predicates.mona /usr/local/lib/mona_predicates.mona
	coqtop -compile decidez
	cp decidez.vo /usr/local/lib/decidez.vo
	./hip --build-image true
	cp MyImage /usr/local/lib/MyImage
