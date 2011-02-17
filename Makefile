OCAMLBUILD = ocamlbuild

# number of parallel jobs, 0 means unlimited.
JOBS = 0

LIBS = unix,str,graph,xml-light
INCLUDES = -I,+ocamlgraph,-I,$(CURDIR)/xml
FLAGS = $(INCLUDES),-g
OB_FLAGS = -no-links -libs $(LIBS) -cflags $(FLAGS) -lflags $(FLAGS) -yaccflag -v -j $(JOBS)

GUI_LIBS = $(LIBS),lablgtk,lablgtksourceview2
GUI_INCLUDES = $(INCLUDES),-I,+lablgtk2
GUI_FLAGS = $(GUI_INCLUDES),-g
OB_GUI_FLAGS = -no-links -libs $(GUI_LIBS) -cflags $(GUI_FLAGS) -lflags $(GUI_FLAGS) -yaccflag -v -j $(JOBS)

all: native
byte: hip.byte sleek.byte
native: hip.native sleek.native
gui: gsleek.byte ghip.byte

hip: hip.native

hip.byte:
	$(OCAMLBUILD) $(OB_FLAGS) main.byte
	cp _build/main.byte hip.byte

hip.native:
	$(OCAMLBUILD) $(OB_FLAGS) main.native
	cp _build/main.native hip

sleek: sleek.native

sleek.byte:
	$(OCAMLBUILD) $(OB_FLAGS) sleek.byte
	cp _build/sleek.byte sleek.byte

sleek.native:
	$(OCAMLBUILD) $(OB_FLAGS) sleek.native
	cp _build/sleek.native sleek

gsleek.byte:
	$(OCAMLBUILD) $(OB_GUI_FLAGS) gsleek.byte
	cp _build/gsleek.byte gsleek

ghip.byte:
	$(OCAMLBUILD) $(OB_GUI_FLAGS) ghip.byte
	cp _build/ghip.byte ghip

# Clean up
clean:
	$(OCAMLBUILD) -quiet -clean 
	rm -f sleek sleek.norm hip hip.norm gsleek ghip
	rm -f allinput.*
