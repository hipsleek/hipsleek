all:parser clean

parser:lexer.cmo parser.cmo main.cmo array_pred.cmo
	ocamlc -o parser lexer.cmo parser.cmo array_pred.cmo main.cmo

lexer.cmo:lexer.ml parser.cmi
	ocamlc -c lexer.ml

lexer.ml:lexer.mll
	ocamllex lexer.mll

parser.mli parser.ml:parser.mly
	ocamlyacc parser.mly

parser.cmi:parser.mli array_pred.cmo
	ocamlc -c parser.mli 

array_pred.cmo:array_pred.ml
	ocamlc -c array_pred.ml

parser.cmo:parser.ml
	ocamlc -c parser.ml

main.cmo:main.ml
	ocamlc -c main.ml

.PHONY:clean
clean:
	rm *.cmi *.cmo parser.ml lexer.ml parser.mli
