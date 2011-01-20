OCAMLBUILD = ocamlbuild

# number of parallel jobs, 0 means unlimited.
JOBS = 0

LIBS = unix,str,graph,xml-light
INCLUDES = -I,+ocamlgraph,-I,$(CURDIR)/xml
FLAGS = $(INCLUDES)
OB_FLAGS = -no-links -libs $(LIBS) -cflags $(FLAGS) -lflags $(FLAGS) -j $(JOBS)

GUI_LIBS = $(LIBS),lablgtk,lablgtksourceview2
GUI_INCLUDES = $(INCLUDES),-I,+lablgtk2
GUI_FLAGS = $(GUI_INCLUDES)
OB_GUI_FLAGS = -no-links -libs $(GUI_LIBS) -cflags $(GUI_FLAGS) -lflags $(GUI_FLAGS) -j $(JOBS)

all: byte
byte: hip.byte sleek.byte
native: hip.native sleek.native
gui: gsleek.byte

hip.byte:
	$(OCAMLBUILD) $(OB_FLAGS) main.byte
	cp _build/main.byte hip 

hip: hip.byte

hip.native:
	$(OCAMLBUILD) $(OB_FLAGS) main.native
	cp _build/main.native hip.opt

hip.opt: hip.native

sleek.byte:
	$(OCAMLBUILD) $(OB_FLAGS) sleek.byte
	cp _build/sleek.byte sleek

sleek: sleek.byte

sleek.native:
	$(OCAMLBUILD) $(OB_FLAGS) sleek.native
	cp _build/sleek.native sleek.opt

sleek.opt: sleek.native

gsleek.byte:
	$(OCAMLBUILD) $(OB_GUI_FLAGS) gsleek.byte
	cp _build/gsleek.byte gsleek

# Clean up
clean:
	$(OCAMLBUILD) -quiet -clean 
	rm -f sleek sleek.opt hip hip.opt
	rm -f allinput.*
