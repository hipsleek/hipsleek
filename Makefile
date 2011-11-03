OCAMLBUILD = ocamlbuild

# number of parallel jobs, 0 means unlimited.
JOBS = 0

# dynlink should precede camlp4lib
LIBS = unix,str,graph,xml-light,dynlink,camlp4lib
LIBS2 = unix,str,graph,xml-light,lablgtk,lablgtksourceview2,dynlink,camlp4lib

INCLUDES = -I,+ocamlgraph,-I,$(CURDIR)/xml,-I,+lablgtk2,-I,+camlp4

FLAGS = $(INCLUDES),-g,-annot

# -no-hygiene flag to disable "hygiene" rules
OB_FLAGS = -no-links -libs $(LIBS) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) 

OBG_FLAGS = -no-links -libs $(LIBS2) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) 

XML = cd $(CURDIR)/xml; make all; make opt; cd ..

all: native 
#gui
byte: hip.byte sleek.byte
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

hip.byte: xml
	@ocamlbuild $(OB_FLAGS) main.byte
	cp -u _build/main.byte p-hip

hip.native: xml
	@ocamlbuild $(OB_FLAGS) main.native
	cp -u _build/main.native hip

sleek.byte: xml
	@ocamlbuild $(OB_FLAGS) sleek.byte
	cp -u _build/sleek.byte p-sleek

sleek.native: xml
	@ocamlbuild $(OB_FLAGS) sleek.native
	cp -u _build/sleek.native sleek

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
