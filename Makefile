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
LIBS2 = unix,str,xml-light,lablgtk,lablgtksourceview2,dynlink,camlp4lib

INCLUDES = -I,$(CURDIR)/header,-I,$(CURDIR)/xml,-I,+lablgtk2,-I,+camlp4,-I,$(INCLPRE)/batteries,-I,$(INCLPRE)/extlib,-I,$(LIBIGRAPH)

PROPERERRS = -warn-error,+4+8+9+11+12+25+28

#FLAGS = $(INCLUDES),-g,-annot,-ccopt,-fopenmp 
FLAGS = $(INCLUDES),$(PROPERERRS),-annot,-ccopt,-fopenmp 
GFLAGS = $(INCLUDES),-g,-annot,-ccopt,-fopenmp 
#GFLAGS = $(INCLUDES),$(PROPERERRS),-g,-annot,-ccopt,-fopenmp 
# ,-cclib,-lz3stubs,-cclib,-lz3,/usr/local/lib/ocaml/libcamlidl.a

# -no-hygiene flag to disable "hygiene" rules
OBB_GFLAGS = -no-links -libs $(LIBSB) -cflags $(GFLAGS) -lflags $(GFLAGS) -lexflag -q -yaccflag -v  -j $(JOBS)
 
OBB_FLAGS = -no-links -libs $(LIBSB) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) 
OBN_FLAGS = -no-links -libs $(LIBSN) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) 

OBG_FLAGS = -no-links -libs $(LIBS2) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) 

XML = cd $(CURDIR)/xml; make all; make opt; cd ..

all: byte decidez.vo 
# gui
byte: sleek.byte hip.byte decidez.vo

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

cmi: clean_cmi all create_cmi

clean_cmi:
	echo 'Temp' > temp.mli
	rm *.mli
	rm -r _build

create_cmi:
	cp _build/*.cmi .
	cp /usr/local/.opam/system/lib/batteries/batString.cmi .
	cp /usr/local/.opam/system/lib/ocamlgraph/graph.cmi .
	ocamlc -i context.ml > context.mli
	ocamlc -i globals.ml > globals.mli
	ocamlc -i auxnorm.ml > auxnorm.mli
	ocamlc -i cformula.ml > cformula.mli
	ocamlc -i iast.ml > iast.mli
	ocamlc -i cast.ml > cast.mli
	ocamlc -i checks.ml > checks.mli
	ocamlc -i cleanUp.ml > cleanUp.mli
	ocamlc -i coq.ml > coq.mli
	ocamlc -i lem_store.ml > lem_store.mli
	ocamlc -i cprinter.ml > cprinter.mli
	ocamlc -i cpure.ml > cpure.mli
	ocamlc -i cvc3.ml > cvc3.mli
	ocamlc -i cvclite.ml > cvclite.mli
	ocamlc -i debug.ml > debug.mli
	ocamlc -i dp.ml > dp.mli
	ocamlc -i env.ml > env.mli
	ocamlc -i error.ml > error.mli
	ocamlc -i exc.ml > exc.mli
	ocamlc -i fixcalc.ml > fixcalc.mli
	ocamlc -i gen.ml > gen.mli
	ocamlc -i globProver.ml > globProver.mli
	ocamlc -i iformula.ml > iformula.mli
	ocamlc -i immutable.ml > immutable.mli
	ocamlc -i infinity.ml > infinity.mli
	ocamlc -i inliner.ml > inliner.mli
	ocamlc -i iprinter.ml > iprinter.mli
	ocamlc -i ipure_D.ml > ipure_D.mli
	ocamlc -i ipure.ml > ipure.mli
	ocamlc -i isabelle.ml > isabelle.mli
	ocamlc -i java.ml > java.mli
	ocamlc -i label_aggr.ml > label_aggr.mli
	ocamlc -i label.ml > label.mli
	ocamlc -i label_only.ml > label_only.mli
	ocamlc -i lem_store.ml > lem_store.mli
	ocamlc -i log.ml > log.mli
	ocamlc -i mathematica.ml > mathematica.mli
	ocamlc -i mcpure_D.ml > mcpure_D.mli
	ocamlc -i mcpure.ml > mcpure.mli
	ocamlc -i minisat.ml > minisat.mli
	ocamlc -i machdep.ml > machdep.mli
	ocamlc -i mem.ml > mem.mli
	ocamlc -i mona.ml > mona.mli
	ocamlc -i net.ml > net.mli
	ocamlc -i omega.ml > omega.mli
	ocamlc -i others.ml > others.mli
	ocamlc -i perm.ml > perm.mli
	ocamlc -i predcomp.ml > predcomp.mli
	ocamlc -i procutils.ml > procutils.mli
	ocamlc -i prooftracer.ml > prooftracer.mli
	ocamlc -i redlog.ml > redlog.mli
	ocamlc -i rtc.ml > rtc.mli
	ocamlc -i rtc_algorithm.ml > rtc_algorithm.mli
	ocamlc -i setmona.ml > setmona.mli
	ocamlc -i share_prover.ml > share_prover.mli
	ocamlc -i share_prover_w.ml > share_prover_w.mli
	ocamlc -i sleekcommons.ml > sleekcommons.mli
	ocamlc -i slicing.ml > slicing.mli
	ocamlc -i smtsolver.ml > smtsolver.mli
	ocamlc -i spass.ml > spass.mli
	ocamlc -i stat_global.ml > stat_global.mli
	ocamlc -i timelog.ml > timelog.mli
	ocamlc -i tpdispatcher.ml > tpdispatcher.mli
	ocamlc -i tree_shares.ml > tree_shares.mli
	ocamlc -i typeinfer.ml > typeinfer.mli
	ocamlc -i wrapper.ml > wrapper.mli
	rm *.cmi
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' cformula.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' cast.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' iast.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' prooftracer.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' immutable.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' env.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' typeinfer.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' sleekcommons.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' log.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' mem.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' stat_global.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' checks.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' rtc.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' cleanUp.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' rtc_algorithm.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' minisat.mli
	sed -i 's/type vertex = vertex$$/type vertex = V.t/' predcomp.mli

mli: create_mli all

files := globals gen ipure iformula cpure cformula cprinter

create_mli:
	cp _build/*.cmi .
	cp /usr/local/.opam/system/lib/batteries/batString.cmi .
	cp /usr/local/.opam/system/lib/ocamlgraph/graph.cmi .
	$(foreach file, $(files), \
		cmp -s $(file).ml mlold/$(file).ml; \
		RETVAL=$$?; \
		if [ $$RETVAL -eq 0 ]; then \
			echo  "SAME"; \
		else \
			cp $(file).ml mlold/$(file).ml; \
			ocamlc -i mlold/$(file).ml > mlold/$(file).mli; \
			sed -i 's/type vertex = vertex$$/type vertex = V.t/' mlold/$(file).mli; \
			cmp -s $(file).mli mlold/$(file).mli; \
			RETVAL=$$?; \
			if [ $$RETVAL -eq 0 ]; then \
				echo "SAME"; \
			else \
				echo "DIFF"; \
				ocamlc mlold/$(file).mli; \
				mv mlold/$(file).cmi .; \
				cp mlold/$(file).mli .; \
			fi; \
		fi; \
	)
	rm *.cmi