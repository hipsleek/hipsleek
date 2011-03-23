OCAMLBUILD = ocamlbuild

# number of parallel jobs, 0 means unlimited.
JOBS = 0

LIBS = unix,str,graph,xml-light,lablgtk,lablgtksourceview2
INCLUDES = -I,+ocamlgraph,-I,$(CURDIR)/xml,-I,+lablgtk2
FLAGS = $(INCLUDES),-g,-annot
OB_FLAGS = -no-links -libs $(LIBS) -cflags $(FLAGS) -lflags $(FLAGS) -yaccflag -v -j $(JOBS)

all: native gui
byte: hip.byte sleek.byte
native: hip.native sleek.native
gui: ghip.native gsleek.native
byte-gui: ghip.byte gsleek.byte

hip: hip.native
sleek: sleek.native
ghip: ghip.native
gsleek: gsleek.native

hip.byte:
	$(OCAMLBUILD) $(OB_FLAGS) main.byte
	cp _build/main.byte hip.byte

hip.native:
	$(OCAMLBUILD) $(OB_FLAGS) main.native
	cp _build/main.native hip

sleek.byte:
	$(OCAMLBUILD) $(OB_FLAGS) sleek.byte
	cp _build/sleek.byte .

sleek.native:
	$(OCAMLBUILD) $(OB_FLAGS) sleek.native
	cp _build/sleek.native sleek

gsleek.byte:
	$(OCAMLBUILD) $(OB_FLAGS) gsleek.byte
	cp _build/gsleek.byte .

gsleek.native:
	$(OCAMLBUILD) $(OB_FLAGS) gsleek.native
	cp _build/gsleek.native gsleek

ghip.byte:
	$(OCAMLBUILD) $(OB_FLAGS) ghip.byte
	cp _build/ghip.byte .

ghip.native:
	$(OCAMLBUILD) $(OB_FLAGS) ghip.native
	cp _build/ghip.native ghip

# Clean up
clean:
	$(OCAMLBUILD) -quiet -clean 
	rm -f sleek sleek.norm hip hip.norm gsleek ghip
	rm -f allinput.*
