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
JOBS = 0

# dynlink should precede camlp4lib
LIBSB = unix,str,xml-light,dynlink,camlp4lib,nums,$(LIBBATLIB),$(LIBELIB),$(LIBGLIB)
LIBSN = unix,str,xml-light,dynlink,camlp4lib,nums,$(LIBBATLIB),$(LIBELIB),$(LIBGLIB)
#,z3
LIBS2 = unix,str,xml-light,lablgtk,lablgtksourceview2,dynlink,camlp4lib

INCLUDES = -I,$(CURDIR)/xml,-I,+lablgtk2,-I,+camlp4,-I,$(INCLPRE)/batteries,-I,$(INCLPRE)/extlib,-I,$(LIBIGRAPH)

PROPERERRS = -warn-error,+4+8+9+11+12+25+28

#FLAGS = $(INCLUDES),-g,-annot,-ccopt,-fopenmp 
FLAGS = $(INCLUDES),$(PROPERERRS),-annot,-ccopt,-fopenmp
FLAGS1 = $(FLAGS),-output-obj
GFLAGS = $(INCLUDES),$(PROPERERRS),-g,-annot,-ccopt,-fopenmp 
# ,-cclib,-lz3stubs,-cclib,-lz3,/usr/local/lib/ocaml/libcamlidl.a

# -no-hygiene flag to disable "hygiene" rules
OBB_GFLAGS = -no-links -libs $(LIBSB) -cflags $(GFLAGS) -lflags $(GFLAGS) -lexflag -q -yaccflag -v  -j $(JOBS)
 
OBB_FLAGS = -no-links -libs $(LIBSB) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) 
OBN_FLAGS = -no-links -libs $(LIBSN) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) 
OBNLIB_FLAGS = -libs $(LIBSN) -cflags $(FLAGS) -lflags $(FLAGS1) -lexflag -q -yaccflag -v  -j $(JOBS) 

OBG_FLAGS = -no-links -libs $(LIBS2) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v -j $(JOBS) 

XML = cd $(CURDIR)/xml; make all; make opt; cd ..


#======================================================================
# tedious stuff for compiling sleek as a library callable from C
LIBOCCMDFLAGS = -c -I /home/cristian/priv/work/working_sleekex/default/xml -I +lablgtk2 -I +camlp4 -I +site-lib/batteries -I +site-lib/extlib -I +ocamlgraph
LIBOLNKFLAGS = unix,str,xml-light,dynlink,camlp4lib,nums,site-lib/batteries,site-lib/extlib,graph
LIBOCCMD = ocamlopt.opt $(LIBOCCMDFLAGS)
LIBOCCMDP4 = ocamlopt.opt -pp camlp4of $(LIBOCCMDFLAGS)
# end of tedious stuff related to the library
#======================================================================
 


all: gbyte decidez.vo 
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

#======================================================================	
# tedious stuff for compiling sleek as a library callable from C
#testsleeklib:
#	@ocamlbuild $(OBN_FLAGS) -ocamlopt libTest.cmx
#	@ocamlbuild $(OBNLIB_FLAGS) -ocamlopt libTest.o
#	gcc -g -Wall -Wextra -I. -c libTest.c -o _build/clibTest.o
#	gcc _build/libTest.o _build/clibTest.o -L /usr/local/lib/ocaml -ldl -lm  -lasmrun -o libTest.exe
	
sleeklib:
# for some reason ocamlbuild does not play well with the -output-obj compiler flag, need to do this UGLY stuff
#@ocamlbuild $(OBNLIB_FLAGS) libSleek.o
	$(LIBOCCMD)  globals.ml error.ml gen.ml debug.ml exc.ml label_only.ml label.ml tree_shares.ml cpure.ml globProver.ml ipure_D.ml ipure.ml mcpure_D.ml slicing.ml mcpure.ml
	ocamlyacc -v ocparser.mly
	rm ocparser.mli
	$(LIBOCCMD) -c -g ocparser.ml
	ocamllex -q oclexer.mll
	ocamlyacc -v rlparser.mly
	rm rlparser.mli
	$(LIBOCCMD) -c -g rlparser.ml
	ocamllex -q rllexer.mll
	ocamllex -q lexer.mll
	$(LIBOCCMD) ocparser.ml oclexer.ml procutils.ml omega.ml perm.ml cformula.ml iformula.ml iast.ml cast.ml coq.ml cvc3.ml rlparser.ml rllexer.ml redlog.ml smtsolver.ml cprinter.ml token.ml lexer.ml checkeq.ml checks.ml cvclite.ml dp.ml infinity.ml iprinter.ml isabelle.ml stat_global.ml log.ml rtc_algorithm.ml minisat.ml mona.ml net.ml prooftracer.ml setmona.ml share_prover.ml share_prover_w.ml spass.ml tpdispatcher.ml immutable.ml context.ml env.ml global_var.ml sleekcommons.ml sautility.ml infer.ml pointers.ml inliner.ml mem.ml term.ml solver.ml astsimp.ml
	$(LIBOCCMDP4) parser.ml
	$(LIBOCCMDP4) parse_shape.ml
	$(LIBOCCMDP4) parse_fixbag.ml
	$(LIBOCCMDP4) parse_fix.ml
	$(LIBOCCMD) cjava.ml drawing.ml fixbag.ml fixcalc.ml java.ml lemproving.ml nativefront.ml paralib1.ml paralib1v2.ml predcomp.ml rtc.ml sa.ml typechecker.ml scriptarguments.ml xmlfront.ml sleekengine.ml sleek.ml libSleek.ml
#
	ocamlopt.opt -output-obj -o libSleekO.o unix.cmxa str.cmxa xml/xml-light.cmxa dynlink.cmxa camlp4/camlp4lib.cmxa nums.cmxa site-lib/batteries/batteries.cmxa site-lib/extlib/extLib.cmxa ocamlgraph/graph.cmxa globals.cmx error.cmx gen.cmx debug.cmx exc.cmx label_only.cmx label.cmx tree_shares.cmx cpure.cmx globProver.cmx ipure_D.cmx ipure.cmx mcpure_D.cmx slicing.cmx mcpure.cmx ocparser.cmx oclexer.cmx procutils.cmx omega.cmx perm.cmx cformula.cmx iformula.cmx iast.cmx cast.cmx coq.cmx cvc3.cmx rlparser.cmx rllexer.cmx redlog.cmx smtsolver.cmx cprinter.cmx token.cmx lexer.cmx checkeq.cmx checks.cmx cvclite.cmx dp.cmx infinity.cmx iprinter.cmx isabelle.cmx stat_global.cmx log.cmx rtc_algorithm.cmx minisat.cmx mona.cmx net.cmx prooftracer.cmx setmona.cmx share_prover.cmx share_prover_w.cmx spass.cmx tpdispatcher.cmx immutable.cmx context.cmx env.cmx global_var.cmx parse_shape.cmx sleekcommons.cmx parser.cmx sautility.cmx infer.cmx inliner.cmx mem.cmx pointers.cmx term.cmx solver.cmx astsimp.cmx cjava.cmx drawing.cmx parse_fixbag.cmx fixbag.cmx parse_fix.cmx fixcalc.cmx java.cmx lemproving.cmx nativefront.cmx paralib1.cmx paralib1v2.cmx predcomp.cmx rtc.cmx sa.cmx typechecker.cmx scriptarguments.cmx xmlfront.cmx sleekengine.cmx sleek.cmx libSleek.cmx 
#
	gcc -g -Wall -Wextra -I. -c libSleekC.c -o libSleekC.o
	
libtest:
	gcc -g -Wall -Wextra -I. -c libSleekUsage.c -o libSleekUsage.o
	gcc libSleekUsage.o libSleekC.o libSleekO.o  -L /usr/local/lib/ocaml -ldl -lm  -lasmrun -lunix -lcamlstr -lnums -o libTest
#	@ocamlbuild $(OBN_FLAGS) sleek.native	

# end of tedious stuff for compiling sleek as a library callable from C
#======================================================================

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
