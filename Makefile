OCAMLC=ocamlc
OCAMLOPT=ocamlopt.opt
OCAMLDEP=ocamldep
OCAMLDOC=ocamldoc

DIRS=.
INCLUDES=-I ./xml
#OCAMLFLAGS=-dtypes $(INCLUDES)    # add other options for ocamlc here
#OCAMLOPTFLAGS=-dtypes $(INCLUDES) # add other options for ocamlopt here
OCAMLFLAGS= -dtypes $(INCLUDES) # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) -p # add other options for ocamlopt here
OCAMLYACC=ocamlyacc
OCAMLYACCFLAGS=-v
OCAMLLEX=ocamllex -q
BIN=../bin
DOC=../doc
DOC_SRC=*/*.ml */*.mli
DEP_DOT_FILE=$(DOC)/depend/dependencies.dot
DEP_PS_FILE=$(DOC)/depend/dependencies.ps
DEP_PDF_FILE=$(DOC)/depend/dependencies.pdf

all: hip sleek prover

opt: hip.opt sleek.opt prover.opt

sparser.cmo sparser.ml: sparser.mly
	$(OCAMLYACC) $(OCAMLYACCFLAGS) sparser.mly
	rm sparser.mli
	$(OCAMLC) $(OCAMLFLAGS) -c -g sparser.ml

slexer.cmo slexer.ml: slexer.mll sparser.ml
	$(OCAMLLEX) slexer.mll
	$(OCAMLC) $(OCAMLFLAGS) -c -g slexer.ml

iparser.cmo iparser.ml: iparser.mly
	$(OCAMLYACC) $(OCAMLYACCFLAGS) iparser.mly
	rm iparser.mli
	$(OCAMLC) $(OCAMLFLAGS) -c -g iparser.ml

ilexer.cmo ilexer.ml: ilexer.mll iparser.ml
	$(OCAMLLEX) ilexer.mll
	$(OCAMLC) $(OCAMLFLAGS) -c -g ilexer.ml

ocparser.cmo ocparser.ml: ocparser.mly
	$(OCAMLYACC) $(OCAMLYACCFLAGS) ocparser.mly
	rm ocparser.mli
	$(OCAMLC) $(OCAMLFLAGS) -c -g ocparser.ml

oclexer.cmo oclexer.ml: oclexer.mll ocparser.ml
	$(OCAMLLEX) oclexer.mll
	$(OCAMLC) $(OCAMLFLAGS) -c -g oclexer.ml

MAIN_FILES=globals.cmo error.cmo util.cmo debug.cmo \
	cpure.cmo ipure.cmo \
	iformula.cmo iast.cmo \
	iparser.cmo ilexer.cmo \
	iprinter.cmo \
	cformula.cmo cast.cmo cprinter.cmo \
	ocparser.cmo oclexer.cmo unix_add.cmo isabelle.cmo coq.cmo omega.cmo mona.cmo setmona.cmo redlog.cmo \
    net.cmo \
	cvclite.cmo smtsolver.cmo tpdispatcher.cmo paralib1.cmo paralib1v2.cmo\
	prooftracer.cmo context.cmo solver.cmo \
	drawing.cmo \
	env.cmo checks.cmo \
	inliner.cmo \
	astsimp.cmo \
	java.cmo cjava.cmo predcomp.cmo rtc.cmo \
	typechecker.cmo \
	globalvars.cmo \
	main.cmo

MAIN_FILES_OPT=globals.cmx error.cmx util.cmx debug.cmx \
	net.cmx \
	cpure.cmx ipure.cmx \
	iformula.cmx iast.cmx \
	iparser.cmx ilexer.cmx \
	iprinter.cmx \
	cformula.cmx cast.cmx cprinter.cmx \
	ocparser.cmx oclexer.cmx unix_add.cmx isabelle.cmx coq.cmx mona.cmx omega.cmx setmona.cmx redlog.cmx \
	cvclite.cmx smtsolver.cmx tpdispatcher.cmx paralib1.cmx paralib1v2.cmx\
	prooftracer.cmx context.cmx solver.cmx \
	drawing.cmx \
	env.cmx checks.cmx inliner.cmx astsimp.cmx \
	typechecker.cmx \
	java.cmx cjava.cmx predcomp.cmx rtc.cmx \
	globalvars.cmx \
	main.cmx

MAIN_FILES_2=util.cmx debug.cmx globals.cmx \
	ipure.cmx iformula.cmx iast.cmx \
	iparser.cmx ilexer.cmx \
	iprinter.cmx

SLEEK_FILES=globals.cmo error.cmo util.cmo debug.cmo \
	cpure.cmo ipure.cmo \
	iformula.cmo iast.cmo \
	cformula.cmo cast.cmo cprinter.cmo \
	sleekcommons.cmo \
	sparser.cmo slexer.cmo iparser.cmo ilexer.cmo \
	iprinter.cmo \
	ocparser.cmo oclexer.cmo unix_add.cmo isabelle.cmo coq.cmo omega.cmo mona.cmo setmona.cmo redlog.cmo \
    net.cmo \
	cvclite.cmo smtsolver.cmo tpdispatcher.cmo paralib1.cmo paralib1v2.cmo\
	prooftracer.cmo context.cmo solver.cmo \
	drawing.cmo \
	env.cmo checks.cmo \
	inliner.cmo \
	astsimp.cmo \
	java.cmo cjava.cmo predcomp.cmo rtc.cmo \
	typechecker.cmo \
	xmlfront.cmo nativefront.cmo \
	sleekengine.cmo \
	sleek.cmo

SLEEK_FILES_OPT=globals.cmx error.cmx util.cmx debug.cmx \
	cpure.cmx ipure.cmx \
	iformula.cmx iast.cmx \
	iparser.cmx ilexer.cmx \
	iprinter.cmx \
	cformula.cmx cast.cmx cprinter.cmx \
	ocparser.cmx oclexer.cmx unix_add.cmx isabelle.cmx coq.cmx omega.cmx mona.cmx setmona.cmx redlog.cmx \
    net.cmx \
	cvclite.cmx smtsolver.cmx tpdispatcher.cmx paralib1.cmx paralib1v2.cmx\
	prooftracer.cmx context.cmx solver.cmx \
	drawing.cmx \
	env.cmx checks.cmx \
	inliner.cmx \
	astsimp.cmx \
	java.cmx cjava.cmx predcomp.cmx rtc.cmx \
	typechecker.cmx \
	sleekcommons.cmx \
	sparser.cmx slexer.cmx \
	xmlfront.cmx nativefront.cmx \
	sleekengine.cmx \
	sleek.cmx

MAIN_FILES_2=util.cmo debug.cmo globals.cmo \
	ipure.cmo iformula.cmo iast.cmo \
	iparser.cmo ilexer.cmo \
	iprinter.cmo


PROVE_FILES=globals.cmo error.cmo util.cmo debug.cmo \
	cpure.cmo ipure.cmo \
	iformula.cmo iast.cmo \
	iparser.cmo ilexer.cmo \
	iprinter.cmo \
	cformula.cmo cast.cmo cprinter.cmo \
	ocparser.cmo oclexer.cmo unix_add.cmo isabelle.cmo coq.cmo omega.cmo mona.cmo setmona.cmo redlog.cmo \
    net.cmo \
	cvclite.cmo smtsolver.cmo tpdispatcher.cmo paralib1.cmo paralib1v2.cmo\
	prooftracer.cmo context.cmo solver.cmo \
	drawing.cmo \
	env.cmo checks.cmo \
	inliner.cmo \
	astsimp.cmo \
	java.cmo cjava.cmo predcomp.cmo rtc.cmo \
	typechecker.cmo \
	prove.cmo

PROVE_FILES_OPT=globals.cmx error.cmx util.cmx debug.cmx \
	cpure.cmx ipure.cmx \
	iformula.cmx iast.cmx \
	iparser.cmx ilexer.cmx \
	iprinter.cmx \
	cformula.cmx cast.cmx cprinter.cmx \
	ocparser.cmx oclexer.cmx unix_add.cmx isabelle.cmx coq.cmx mona.cmx omega.cmx setmona.cmx redlog.cmx \
    net.cmx \
	cvclite.cmx smtsolver.cmx tpdispatcher.cmx paralib1.cmx paralib1v2.cmx\
	prooftracer.cmx context.cmx solver.cmx \
	drawing.cmx \
	env.cmx checks.cmx inliner.cmx astsimp.cmx \
	typechecker.cmx \
	java.cmx cjava.cmx predcomp.cmx rtc.cmx \
	prove.cmx


WEB_FILES=globals.cmo error.cmo util.cmo debug.cmo \
	cpure.cmo ipure.cmo \
	iformula.cmo iast.cmo \
	iparser.cmo ilexer.cmo \
	iprinter.cmo \
	cformula.cmo cast.cmo cprinter.cmo \
	ocparser.cmo oclexer.cmo unix_add.cmo isabelle.cmo coq.cmo omega.cmo mona.cmo setmona.cmo \
    net.cmo \
	cvclite.cmo smtsolver.cmo tpdispatcher.cmo paralib1.cmo paralib1v2.cmo \
	prooftracer.cmo context.cmo solver.cmo \
	drawing.cmo \
	env.cmo checks.cmo \
	inliner.cmo \
	astsimp.cmo \
	java.cmo cjava.cmo predcomp.cmo rtc.cmo \
	typechecker.cmo \
	web.cmo
hip1: $(MAIN_FILES_2)
	$(OCAMLC) -g -o $@ $(OCAMLFLAGS) unix.cma str.cma graph.cma $(MAIN_FILES_2)

hipc:
	make clean; make hip

hip: $(MAIN_FILES)
	$(OCAMLC) -g -o $@ $(OCAMLFLAGS) unix.cma str.cma graph.cma $(MAIN_FILES)

#hip.opt: $(MAIN_FILES:*.cmo=*.cmx)
#	make -f Makefile.opt hip.opt

hip.opt: $(MAIN_FILES_OPT)
	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) unix.cmxa str.cmxa graph.cmxa $(MAIN_FILES_OPT)

prover: $(PROVE_FILES)
	$(OCAMLC) -g -o $@ $(OCAMLFLAGS) unix.cma str.cma graph.cma $(PROVE_FILES)

prover.opt: $(PROVE_FILES_OPT)
	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) unix.cmxa str.cmxa graph.cmxa $(PROVE_FILES_OPT)

	
web: $(WEB_FILES)
	$(OCAMLC) -g -o $@ $(OCAMLFLAGS) unix.cma str.cma graph.cma $(WEB_FILES)

#$(OCAMLC) -g -o $@ $(OCAMLFLAGS) unix.cma str.cma graph.cma $(PROVE_FILES)

sleekc:
	make clean; make sleek 

xml/xml-light.cma:
	make -C xml

xml/xml-light.cmxa:
	make -C xml xml-light.cmxa

sleek: xml/xml-light.cma $(SLEEK_FILES) 
	$(OCAMLC) -g -o $@ $(OCAMLFLAGS) unix.cma str.cma graph.cma xml-light.cma $(SLEEK_FILES)

sleek.opt: xml/xml-light.cmxa $(SLEEK_FILES_OPT) 
	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) unix.cmxa str.cmxa graph.cmxa xml-light.cmxa $(SLEEK_FILES_OPT)

#sleek.opt: xml/xml-light.cmxa $(SLEEK_FILES:*.cmo=*.cmx) 
#	$(OCAMLOPT) -o $@ $(OCAMLOPTFLAGS) unix.cmxa str.cmxa graph.cmxa $(SLEEK_FILES:*.cmo=*.cmx)

CRISTINA_FILES=util.cmo debug.cmo globals.cmo error.cmo \
	cpure.cmo cformula.cmo cast.cmo

cristina: $(CRISTINA_FILES)

TEST_OO_FILES=util.cmo debug.cmo globals.cmo error.cmo \
	cpure.cmo ipure.cmo \
	iformula.cmo iast.cmo \
	checks.cmo \
	iparser.cmo ilexer.cmo \
	iprinter.cmo \
	cformula.cmo cast.cmo cprinter.cmo \
	ocparser.cmo oclexer.cmo unix_add.cmo isabelle.cmo coq.cmo omega.cmo mona.cmo\
	cvclite.cmo smtsolver.cmo tpdispatcher.cmo \
	context.cmo \
	solver.cmo \
	env.cmo astsimp.cmo \
	test-oo.cmo \
#	typechecker.cmo \
#	main.cmo

oo: $(TEST_OO_FILES)
	$(OCAMLC) -g -o $@ $(OCAMLFLAGS) unix.cma str.cma graph.cma $(TEST_OO_FILES)


JAVA_FILES=util.cmo debug.cmo globals.cmo error.cmo \
	cpure.cmo ipure.cmo \
	iformula.cmo iast.cmo iprinter.cmo \
	iparser.cmo ilexer.cmo \
	java.cmo

j: $(JAVA_FILES)
	$(OCAMLC) -g -o $@ $(OCAMLFLAGS) unix.cma str.cma graph.cma $(JAVA_FILES)

# ------------------------------------------------------------
# Common rules
# ------------------------------------------------------------
.SUFFIXES: .ml .mli .cmo .cmi .cmx .mly .mll

.ml.annot:
	$(OCAMLC) $(OCAMLFLAGS) -c -g $<

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c -g $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c -g $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

# Clean up
clean: 
	rm -f slexer.ml ilexer.ml iparser.ml oclexer.ml ocparser.ml *.cmo *.cmi *.cmx *.o *.mli *.output *.annot ss.exe hip.exe hip hip.opt ss ss.opt sleek.opt sleek sleek.exe prover prover.opt web *~ oo oo.exe

# Dependencies
beforedepend: iparser.ml ocparser.ml

depend: beforedepend
	(for d in $(DIRS); \
	do $(OCAMLDEP) $(INCLUDES) $$d/*.mli $$d/*.ml; \
	done) > .depend

-include .depend
# DO NOT DELETE
