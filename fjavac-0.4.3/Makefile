all: demo

javac.exe:
	fslex oscan.mll

	fsc -o ocfgc.exe -r Mono.Posix.dll compat.fs std.ml charx.ml listx.ml arrayx.ml strx.ml \
setx.ml mapx.ml hashx.ml util.ml fa.ml cfg.ml pda.ml scanx.ml \
syntaxx.ml parsex.ml osyntax.ml ocfg.ml oscan.fs parse.ml oparse.ml ocfgc.ml

	mono ocfgc.exe --cache=jpda-fs.cache java.g j

	fslex jscan.mll

	fsc -o javac.exe -r Mono.Posix.dll -r ICSharpCode.SharpZipLib.dll \
compat.fs std.ml charx.ml listx.ml arrayx.ml strx.ml \
setx.ml mapx.ml hashx.ml util.ml fa.ml cfg.ml pda.ml scanx.ml \
syntaxx.ml parsex.ml osyntax.ml ocfg.ml jsyntax.ml jscan.fs parse.ml \
jparse.ml jplain.ml jtyped.ml regex.fs unzip.fs jjar.ml jenv.ml jtyping.ml jasm.ml \
jbytecode.ml jbyteio.ml javac.ml


demo-fs: javac.exe
	mono javac.exe -v test.java

demo: javacx
	./javacx -v test.java


include Makefile.test


#---- modules

clibs=-cclib -lz -custom zlib.o str.cma unix.cma
xlibs=-cclib -lz zlib.o str.cmxa unix.cmxa

# common modules
mods=compat std charx listx arrayx strx setx mapx hashx util \
  fa cfg pda scanx syntaxx parsex osyntax ocfg  

dlls=std charx listx arrayx strx setx mapx hashx util \
  fa cfg pda scanx syntaxx parsex osyntax ocfg  
jc_dlls=$(dlls) jsyntax jscan parse jparse jplain \
  jtyped jjar jenv jtyping jasm jbytecode jbyteio javac


# modules for java compiler 
jc_mods=$(mods) jsyntax jscan parse jparse jplain \
  jtyped unzip regex jjar jenv jtyping jasm jbytecode jbyteio javac

# modules for java precompiler 
jb_mods=$(mods) jsyntax jscan parse jparse javab

# modules for java jar inspector 
jj_mods=$(mods) jsyntax jplain jtyped unzip regex jjar javaj

# modules for cif compiler (c with infomation info)
cc_mods=$(mods) csyntax cscan parse cparse cifc

# modules for ocfg compiler
oc_mods=$(mods) oscan parse oparse ocfgc

all_mods=$(jc_mods) javab javaj oscan oparse ocfgc

objs=javac javacx javab javabx javaj javajx cifc ocfgc ocfgcx \
 oscan.ml jsyntax.ml jscan.mll jscan.ml jparse.ml

jc_cmos=$(addsuffix .cmo, $(jc_mods))
jc_cmxs=$(addsuffix .cmx, $(jc_mods))
jb_cmos=$(addsuffix .cmo, $(jb_mods))
jb_cmxs=$(addsuffix .cmx, $(jb_mods))
jj_cmos=$(addsuffix .cmo, $(jj_mods))
jj_cmxs=$(addsuffix .cmx, $(jj_mods))
cc_cmos=$(addsuffix .cmo, $(cc_mods))
cc_cmxs=$(addsuffix .cmx, $(cc_mods))
oc_cmos=$(addsuffix .cmo, $(oc_mods))
oc_cmxs=$(addsuffix .cmx, $(oc_mods))

# keep these files
.SECONDARY: oscan.ml cscan.ml jscan.ml


#---- binaries

javac: $(jc_cmos) zlib.o
	$(ocamlc) -o $@ $(clibs) $(jc_cmos)

javacx: $(jc_cmxs) zlib.o
	$(ocamlopt) $(xlibs) -o $@ $(jc_cmxs)

javab: $(jb_cmos) 
	$(ocamlc) -o $@ unix.cma $(jb_cmos)

javabx: $(jb_cmxs)
	$(ocamlopt) unix.cmxa -o $@ $(jb_cmxs)

javaj: $(jj_cmos) zlib.o
	$(ocamlc) -o $@ $(clibs) $(jj_cmos)

javajx: $(jj_cmxs) zlib.o
	$(ocamlopt) $(xlibs) -o $@ $(jj_cmxs)

jsyntax.ml jscan.mll jpda.cache jparse.ml: ocfgcx java.g
#	./ocfgcx java.g j --debug-pda 
	./ocfgcx java.g j 

cifc: $(cc_cmos)
	$(ocamlc) -o $@ $(cc_cmos)

cifcx: $(cc_cmxs)
	$(ocamlopt) -o $@ $(cc_cmxs)

csyntax.ml cscan.mll cparse.ml: ocfgcx cif.g
	./ocfgcx cif.g c

ocfgc: $(oc_cmos)
	$(ocamlc) -o $@ unix.cma $^

ocfgcx: $(oc_cmxs)
	$(ocamlopt) unix.cmxa -o $@ $^

bootstrap: ocfgcx java.g
	./ocfgcx ocfg.g o

zlib.o: zlib.c
	$(ocamlc) $<


#---- dependencies for generated files

jscan.cmo: util.cmo
jparse.cmo: jsyntax.cmo jscan.cmo parse.cmo util.cmo
jplain.cmo: jsyntax.cmo 
javac.cmo: jparse.cmo
javab.cmo: jsyntax.cmo jparse.cmo

jscan.cmx: util.cmx
jparse.cmx: jsyntax.cmx jscan.cmx parse.cmx util.cmx
jplain.cmx: jsyntax.cmx
javac.cmx: jparse.cmx
javab.cmx: jsyntax.cmx jparse.cmx

cscan.cmo: util.cmo
cparse.cmo: csyntax.cmo cscan.cmo parse.cmo util.cmo
cplain.cmo: csyntax.cmo 
cifc.cmo: cparse.cmo

cscan.cmx: util.cmx
cparse.cmx: csyntax.cmx cscan.cmx parse.cmx util.cmx
cplain.cmx: csyntax.cmx
cifc.cmx: cparse.cmx

oscan.cmo: util.cmo
oparse.cmo: osyntax.cmo oscan.cmo parse.cmo util.cmo
ocfg.cmo: osyntax.cmo oscan.cmo oparse.cmo 

oscan.cmx: util.cmx
oparse.cmx: osyntax.cmx oscan.cmx parse.cmx util.cmx
ocfg.cmx: osyntax.cmx oscan.cmx oparse.cmx 


#---- patterns

ocamlc=$(if $(shell which ocamlc.opt),ocamlc.opt -g,ocamlc -g)
ocamlopt=$(if $(shell which ocamlopt.opt),ocamlopt.opt,ocamlopt)
ocamllex=$(if $(shell which ocamllex.opt),ocamllex.opt,ocamllex)
ocamldep=$(if $(shell which ocamldep.opt),ocamldep.opt,ocamldep)

%.ml: %.mll
	$(ocamllex) $<

%.cmi: %.mli
	$(ocamlc) -c $<

%.cmo: %.ml
	$(ocamlc) -c $<

%.cmx: %.ml
	$(ocamlopt) -c $<

clean:
	rm -rf ocamlprof.dump gmon.out *.class
	rm -rf .depend *.cmi *.cmo *.cmx *.o *.dll *.exe $(objs)
	@echo
	@echo -e "Try 'make cleanall' if segmentation fault occurs (because of ?pda.cache)."
	@echo

cleanall: clean
	rm -f ?pda.cache ?pda-fs.cache

.depend:
	@echo
	@echo '---- 1) requires ocaml 3.09.1: http://caml.inria.fr'
	@echo '        or fsharp 1.1.9.1: http://research.microsoft.com/projects/ilx/fsharp.aspx'
	@echo '---- 2) requires zip library: apt-get install zlib1g-dev'
	@echo '---- 3) requires jdk 1.5.0 update 5 runtime (rt.jar): http://java.sun.com'
	@echo
	$(ocamldep) *.ml *.mli > .depend


depend:
	rm -f .depend
	$(ocamldep) *.ml *.mli > .depend

include .depend


#---- packages

name=fjavac-0.4.3

files=\
	README README.fs Changelog \
  Makefile Makefile.fs Makefile.test \
  test.java ocfg.el ocfg.g java.g zlib.c \
  compat.fs unzip.fs regex.fs \
	oscan.mll oparse.ml ocfgc.ml \
  $(addsuffix .ml, $(jc_mods)) \
	javab.ml javaj.ml	\
	jjar.mli setx.mli unzip.mli \
  jpda.cache jpda-fs.cache

html:
	rm -rf $(name)
	mkdir $(name)
	cp -a $(files) $(name)
	tar zcf $(name).tgz $(name)
	cp java.g $(name).tgz ~/h/javac
	cd $(name); make demo
