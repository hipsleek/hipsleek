OCAMLBUILD = ocamlbuild

#  number of parallel jobs, 0 means unlimited.
JOBS = 0

# dynlink should precede camlp4lib
LIBSB = unix,str,graph,xml-light,dynlink,camlp4lib,nums,site-lib/batteries/batteries,site-lib/extlib/extLib
LIBSN = unix,str,graph,xml-light,dynlink,camlp4lib,nums,site-lib/batteries/batteries,site-lib/extlib/extLib
#,z3
LIBS2 = unix,str,graph,xml-light,lablgtk,lablgtksourceview2,dynlink,camlp4lib

INCLUDES = -I,+ocamlgraph,-I,$(CURDIR)/xml,-I,$(CURDIR)/cil/obj/x86_LINUX,-I,+big_int,-I,+lablgtk2,-I,+camlp4,-I,+site-lib/batteries,-I,+site-lib/extlib

FLAGS = $(INCLUDES),-g,-annot,-ccopt,-fopenmp 
# ,-cclib,-lz3stubs,-cclib,-lz3,/usr/local/lib/ocaml/libcamlidl.a

# -no-hygiene flag to disable "hygiene" rules
OBB_FLAGS = -no-links -libs $(LIBSB) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) 
OBN_FLAGS = -no-links -libs $(LIBSN) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) 

OBG_FLAGS = -no-links -libs $(LIBS2) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) 

XML = cd $(CURDIR)/xml; make all; make opt; cd ..

all: byte decidez.vo
#gui
byte: hip.byte sleek.byte
#byte: sleek.byte hip.byte test_cilparser.byte
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
	@ocamlbuild $(OBB_FLAGS) main.byte
	cp -u _build/main.byte hip
	cp -u _build/main.byte b-hip

hip.native: xml
	@ocamlbuild $(OBN_FLAGS) main.native
	cp -u _build/main.native hip
	cp -u _build/main.native n-hip

sleek.byte: xml
	@ocamlbuild $(OBB_FLAGS) sleek.byte
	cp -u _build/sleek.byte sleek
	cp -u _build/sleek.byte b-sleek

sleek.native: xml
	@ocamlbuild $(OBN_FLAGS) sleek.native
	cp -u _build/sleek.native sleek
	cp -u _build/sleek.native n-sleek

test_cilparser.byte: xml
	@ocamlbuild $(OBB_FLAGS) test_cilparser.byte
	cp -u _build/test_cilparser.byte test_cilparser
	
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

install-native: hip.native sleek.native
	cp -u _build/main.native /usr/local/bin/hip
	cp -u _build/sleek.native /usr/local/bin/sleek
