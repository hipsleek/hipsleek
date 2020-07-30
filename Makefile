OCAMLBUILD = ocamlbuild

# OPAM repository
OPREP = $(OCAML_TOPLEVEL_PATH)/..
#~/.opam/system/lib
BATLIB = batteries/batteries
ELIB = extlib/extLib
GRLIB = ocamlgraph/graph
OLIBS = $(OPREP)/$(GRLIB),
#CPPO_FLAGS = -pp "cppo -I ../ -D TRACE"
CPPO_FLAGS =

UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
 CPFLAGS = -u
endif
ifeq ($(UNAME_S),Darwin)
 CPFLAGS = 
endif

#CFLAGS1='-Wl,--rpath=/usr/lib-2.12'
#CFLAGS2='-Wl,--dynamic-linker=/usr/lib-2.12/ld-linux.so.2'

ifdef OCAML_TOPLEVEL_PATH
 INCLPRE = $(OPREP)
 LIBBATLIB = $(OPREP)/$(BATLIB)
 LIBELIB = $(OPREP)/$(ELIB)
 LIBGLIB = $(OPREP)/$(GRLIB)
 LIBFILEUTILS = $(OPREP)/fileutils/fileutils
 LIBIGRAPH = $(OPREP)/ocamlgraph
else
 INCLPRE = +site-lib
 LIBBATLIB = site-lib/$(BATLIB)
 LIBELIB = site-lib/$(ELIB)
 LIBGLIB = graph
 LIBIGRAPH = +ocamlgraph
 LIBFILEUTILS = fileutils
endif

#  number of parallel jobs, 0 means unlimited.
JOBS = 16

# dynlink should precede camlp4lib
LIBSB = unix,str,xml-light,dynlink,camlp4lib,nums,$(LIBBATLIB),$(LIBELIB),$(LIBGLIB),$(LIBFILEUTILS)
LIBSN = unix,str,xml-light,dynlink,camlp4lib,nums,$(LIBBATLIB),$(LIBELIB),$(LIBGLIB),$(LIBFILEUTILS)
#,z3
LIBS2 = unix,str,xml-light,lablgtk,lablgtksourceview2,dynlink,camlp4lib

INCLUDES = -I,$(CURDIR)/xml,-I,$(CURDIR)/cil,-I,$(CURDIR)/joust,-I,$(CURDIR)/ints,-I,+lablgtk2,-I,+camlp4,-I,$(INCLPRE)/batteries,-I,$(INCLPRE)/extlib,-I,$(LIBIGRAPH),-I,$(INCLPRE)/fileutils
INCLUDESN = -I,$(CURDIR)/xml,-I,$(CURDIR)/cil,-I,$(CURDIR)/joust,-I,$(CURDIR)/ints,-I,+lablgtk2,-I,$(INCLPRE)/batteries,-I,$(INCLPRE)/extlib,-I,$(LIBIGRAPH),-I,$(INCLPRE)/fileutils

PROPERERRS = -warn-error,+4+8+9+11+12+25+28

#FLAGS = $(INCLUDES),-g,-annot,-ccopt,-fopenmp
FLAGS = $(INCLUDES),$(PROPERERRS),-annot,-bin-annot,-ccopt,-fopenmp #,-ccopt,CFLAGS1,-ccopt,CFLAGS2

GFLAGS = $(INCLUDES),-g,-annot,-bin-annot,-ccopt,-fopenmp
SCFLAGS = $(INCLUDES),$(PROPERERRS),-annot,-bin-annot,-ccopt,-fopenmp #-ccopt,-static,-ccopt,-fPIE
SLFLAGS = $(INCLUDES),$(PROPERERRS),-annot,-bin-annot,-ccopt,-static,-ccopt,-fopenmp #,-ccopt,-pie #,-ccopt,-pic
#FLAGS = $(INCLUDES),-ccopt,-fopenmp
#GFLAGS = $(INCLUDES),-g,-ccopt,-fopenmp
#GFLAGS = $(INCLUDES),$(PROPERERRS),-g,-annot,-ccopt,-fopenmp
# ,-cclib,-lz3stubs,-cclib,-lz3,/usr/local/lib/ocaml/libcamlidl.a

# -no-hygiene flag to disable "hygiene" rules
OBB_GFLAGS = -no-links -libs $(LIBSB) -cflags $(GFLAGS) -lflags $(GFLAGS) -lexflag -q -yaccflag -v  -j $(JOBS)  $(CPPO_FLAGS)
OBB_NGFLAGS = -no-links -libs $(LIBSB) -cflags $(GFLAGS) -lflags $(GFLAGS) -lexflag -q -yaccflag -v  -j $(JOBS)

OBB_FLAGS = -no-links -libs $(LIBSB) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) $(CPPO_FLAGS)
OBN_FLAGS = -no-links -libs $(LIBSN) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) $(CPPO_FLAGS)

#static - incl C libs
OBNS_FLAGS = -no-links -libs $(LIBSN) -cflags $(SCFLAGS) -lflags $(SLFLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) $(CPPO_FLAGS)

OBG_FLAGS = -no-links -libs $(LIBS2) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) $(CPPO_FLAGS)

XML = cd $(CURDIR)/xml; make all; make opt; cd ..

all: byte # decidez.vo
# gui
byte: sleek.byte hip.byte # decidez.vo

sh_proc: sh_proc.byte

gbyte: sleek.gbyte hip.gbyte

test: dtest.byte

# hsprinter.byte
native: hip.native sleek.native
static: ship.native ssleek.native
gui: ghip.native gsleek.native
byte-gui: ghip.byte gsleek.byte

hip: hip.native
sleek: sleek.native
ghip: ghip.native
gsleek: gsleek.native

xml: xml/xml-light.cma

xml/xml-light.cma:
	$(XML)

ppx: ppx
	@ocamlbuild $(OBB_NGFLAGS) ppx/ex1.byte

parser.cmo:
	@ocamlbuild $(OBB_NGFLAGS) parser.cmo

dtest.byte: xdebug.cppo
	@ocamlbuild $(OBB_GFLAGS) dtest.byte
	cp $(CPFLAGS) _build/dtest.byte dtest

hip.gbyte: xml parser.cmo
	@ocamlbuild $(OBB_GFLAGS) main.byte
	cp $(CPFLAGS) _build/main.byte hip
	cp $(CPFLAGS) _build/main.byte g-hip

sleek.gbyte: xml parser.cmo
	@ocamlbuild $(OBB_GFLAGS) sleek.byte
	cp $(CPFLAGS) _build/sleek.byte sleek
	cp $(CPFLAGS) _build/sleek.byte g-sleek

sh_proc.byte:
	@ocamlbuild -cflags -annot $(OBB_GFLAGS) sh_proc.byte
	cp $(CPFLAGS) _build/sh_proc.byte sh_proc

hip.byte: xml
	@ocamlbuild $(OBB_FLAGS) main.byte
	cp $(CPFLAGS) _build/main.byte hip
	cp $(CPFLAGS) _build/main.byte b-hip

sleek.byte: xml
	@ocamlbuild $(OBB_FLAGS) sleek.byte
	cp $(CPFLAGS) _build/sleek.byte sleek
	cp $(CPFLAGS) _build/sleek.byte b-sleek

hip.native: xml
	@ocamlbuild $(OBN_FLAGS) main.native
	cp $(CPFLAGS) _build/main.native hip
	cp $(CPFLAGS) _build/main.native n-hip

ship.native: xml
	@ocamlbuild $(OBNS_FLAGS) main.native
	cp $(CPFLAGS) _build/main.native hip
	cp $(CPFLAGS) _build/main.native s-hip

hsprinter.byte: xml
	@ocamlbuild $(OB_FLAGS) hsprinter.byte

sleek.native: xml
	@ocamlbuild $(OBN_FLAGS) sleek.native
	cp $(CPFLAGS) _build/sleek.native sleek
	cp $(CPFLAGS) _build/sleek.native n-sleek

ssleek.native: xml
	@ocamlbuild $(OBNS_FLAGS) sleek.native
	cp $(CPFLAGS) _build/sleek.native sleek
	cp $(CPFLAGS) _build/sleek.native s-sleek

gsleek.byte:
	@ocamlbuild $(OBG_FLAGS) gsleek.byte
	cp $(CPFLAGS) _build/gsleek.byte p-gsleek

gsleek.native:
	@ocamlbuild $(OBG_FLAGS) gsleek.native
	cp $(CPFLAGS) _build/gsleek.native gsleek

fact.byte:
	@ocamlbuild $(OBB_FLAGS) fact.byte
	cp $(CPFLAGS) _build/fact.byte fact

ghip.byte:
	@ocamlbuild $(OBG_FLAGS) ghip.byte
	cp $(CPFLAGS) _build/ghip.byte p-ghip

ghip.native:
	@ocamlbuild $(OBG_FLAGS) ghip.native
	cp $(CPFLAGS) _build/ghip.native ghip

# Clean up
clean:
	$(OCAMLBUILD) -quiet -clean
	rm -f sleek sleek.norm hip hip.norm gsleek ghip sleek.byte hip.byte
	rm -f *.cmo *.cmi *.cmx *.o *.mli *.output *.annot slexer.ml ilexer.ml lexer.ml iparser.ml oclexer.ml ocparser.ml rlparser.ml rllexer.ml *.depends
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
	cp $(CPFLAGS) _build/main.native /usr/local/bin/hip
	cp $(CPFLAGS) _build/sleek.native /usr/local/bin/sleek

FILES := globals tree_shares rtc_algorithm net machdep globProver error gen others ipure_D debug timelog procutils label_only label exc ipure iformula cpure smtsolver setmona omega redlog wrapper mcpure_D slicing mcpure perm mathematica label_aggr isabelle cvclite cvc4 coq iast inliner checks cformula cleanUp cprinter stat_global spass prooftracer predcomp minisat log mona iprinter java infinity immutable fixcalc dp cast cfutil sleekcommons rtc mem lem_store env auxnorm context share_prover share_prover_w tpdispatcher typeinfer imminfer

init: clean_mli all create_mli

clean_mli:
	echo 'Temp' > temp.mli
	rm *.mli
	rm -r _build

create_mli:
	cp _build/*.cmi .
	cp /usr/local/.opam/system/lib/batteries/batString.cmi .
	cp /usr/local/.opam/system/lib/ocamlgraph/graph.cmi .
	# cp /usr/local/lib/ocaml/camlp4/Camlp4.cmi .
	# cp /usr/local/lib/ocaml/camlp4/Camlp4_import.cmi .
	$(foreach file, $(FILES), \
		ocamlc -i $(file).ml > $(file).mli; \
		sed -i 's/type vertex = vertex$$/type vertex = V.t/' $(file).mli; \
	)
	rm *.cmi
	mkdir -p mlold
	cp --preserve *.ml mlold/

mli: change_mli all

change_mli:
	cp _build/*.cmi .
	cp /usr/local/.opam/system/lib/batteries/batString.cmi .
	cp /usr/local/.opam/system/lib/ocamlgraph/graph.cmi .
	# cp /usr/local/lib/ocaml/camlp4/Camlp4.cmi .
	# cp /usr/local/lib/ocaml/camlp4/Camlp4_import.cmi .
	$(foreach file, $(FILES), \
		TIME1=$(shell stat -c %Y $(file).ml); \
		TIME2=$(shell stat -c %Y mlold/$(file).ml); \
		if [ $$TIME1 -eq $$TIME2 ]; then \
			echo "SAME" $(file); \
		else \
			cp --preserve $(file).ml mlold/$(file).ml; \
			ocamlc -i mlold/$(file).ml > mlold/$(file).mli; \
			sed -i 's/type vertex = vertex$$/type vertex = V.t/' mlold/$(file).mli; \
			cmp -s $(file).mli mlold/$(file).mli; \
			RETVAL=$$?; \
			if [ $$RETVAL -eq 0 ]; then \
			 	echo "SAME" $(file); \
			else \
			 	echo "DIFF" $(file); \
			 	ocamlc mlold/$(file).mli; \
			 	mv mlold/$(file).cmi .; \
			 	cp mlold/$(file).mli .; \
			fi; \
		fi; \
	)
	rm *.cmi
