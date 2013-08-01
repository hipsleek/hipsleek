OCAMLBUILD = ocamlbuild


# OPAM repository
OPREP = $(OCAML_TOPLEVEL_PATH)/..
#~/.opam/system/lib
BATLIB = batteries/batteries
ELIB = extlib/extLib
GRLIB = ocamlgraph/graph
OLIBS = $(OPREP)/$(GRLIB),

ifdef OCAML_TOPLEVEL_PATH
 INCLPRE = $(OPREP)
 LIBBATLIB = $(OPREP)/$(BATLIB)
 LIBELIB = $(OPREP)/$(ELIB)
 LIBGLIB = $(OPREP)/$(GRLIB)
 LIBIGRAPH = $(OPREP)/ocamlgraph
else
 INCLPRE = +site-lib
 LIBBATLIB = site-lib/$(BATLIB)
 LIBELIB = site-lib/$(ELIB)
 LIBGLIB = graph
 LIBIGRAPH = +ocamlgraph
endif

#  number of parallel jobs, 0 means unlimited.
JOBS = 16

# dynlink should precede camlp4lib
LIBSB = unix,str,xml-light,dynlink,camlp4lib,nums,$(LIBBATLIB),$(LIBELIB),$(LIBGLIB)
LIBSN = unix,str,xml-light,dynlink,camlp4lib,nums,$(LIBBATLIB),$(LIBELIB),$(LIBGLIB)
#,z3
LIBS2 = unix,str,xml-light,lablgtk,lablgtksourceview2,dynlink,camlp4lib,libcamlidl

INCLUDES = -I,$(CURDIR)/xml,-I,+lablgtk2,-I,+camlp4,-I,$(INCLPRE)/batteries,-I,$(INCLPRE)/extlib,-I,$(LIBIGRAPH)

PROPERERRS = -warn-error,+4+8+9+11+12+25+28

#FLAGS = $(INCLUDES),-g,-annot,-ccopt,-fopenmp 
FLAGS = $(INCLUDES),$(PROPERERRS),-annot,-ccopt,-fopenmp 
GFLAGS = $(INCLUDES),$(PROPERERRS),-g,-annot,-ccopt,-fopenmp 
# ,-cclib,-lz3stubs,-cclib,-lz3,/usr/local/lib/ocaml/libcamlidl.a

# -no-hygiene flag to disable "hygiene" rules
OBB_GFLAGS = -no-links -libs $(LIBSB) -cflags $(GFLAGS) -lflags $(GFLAGS) -lexflag -q -yaccflag -v  -j $(JOBS)
 
OBB_FLAGS = -no-links -libs $(LIBSB) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) 
OBN_FLAGS = -no-links -libs $(LIBSN) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) 

OBG_FLAGS = -no-links -libs $(LIBS2) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) 

XML = cd $(CURDIR)/xml; make all; make opt; cd ..

all: byte decidez.vo 
#gui
byte: sleek.byte hip.byte

gbyte: sleek.gbyte hip.gbyte
 
# hsprinter.byte
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

hip.gbyte: xml
	@ocamlbuild $(OBB_GFLAGS) main.byte
	cp -u _build/main.byte hip
	cp -u _build/main.byte g-hip

sleek.gbyte: xml
	@ocamlbuild $(OBB_GFLAGS) sleek.byte
	cp -u _build/sleek.byte sleek
	cp -u _build/sleek.byte g-sleek

hip.byte: xml
	@ocamlbuild $(OBB_FLAGS) main.byte
	cp -u _build/main.byte hip
	cp -u _build/main.byte b-hip

sleek.byte: xml
	@ocamlbuild $(OBB_FLAGS) sleek.byte
	cp -u _build/sleek.byte sleek
	cp -u _build/sleek.byte b-sleek

hip.native: xml
	@ocamlbuild $(OBN_FLAGS) main.native
	cp -u _build/main.native hip
	cp -u _build/main.native n-hip

hsprinter.byte: xml
	@ocamlbuild $(OB_FLAGS) hsprinter.byte

sleek.native: xml
	@ocamlbuild $(OBN_FLAGS) sleek.native
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

install-native: hip.native sleek.native
	cp -u _build/main.native /usr/local/bin/hip
	cp -u _build/sleek.native /usr/local/bin/sleek
