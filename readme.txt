
sleek/hip parser : parser.ml
tokenizer : lexer.mll

sleek : sleek.ml
hip   : main.ml

input language : iast.ml, iformula.ml, ipure.ml
core language : cast.mk, cformula.ml, cpure.ml

transformer from input --> core language : 

globals :
   globals.ml (hip/sleek specific globals) 
   VarGen.ml (global vars)
   gen.ml (general utility)
   debug.ml (debug utilities)

debugging commands : 
   x_add (add line tracing to debug call, at least 2 para)
   x_add_1 (add line tracing to debug call, at least 1 para)
   x_binfo_hprint (always print)
   x_ninfo_hprint  (no printing)
   x_tinfo_hprint  (selective trace printing)

running sleek:
 sleek demo.slk
selective debugging
 sleek demo.slk -dre "..regular expr on method name.."
dumping all trace:
 sleek demo.slk -dd
dumping proof log:
 sleek demo.slk --esl

Compilation
===========

make // to make bytecode for hip/sleek

make native // to make native compiled code for hip/sleek


Test Suite (to check prior to merging with default)
===================================================
cd examples/working
./run-fast-tests.pl sleek
./run-fast-tests.pl hip -flags "--eps"

Debugging
=========
cd demo

../sleek ex21e2-heap-node.slk -dre ".*imply" 

Tracing
=======
dd.log
------
#heap_entail_conjunct_helper,Loop
#heap_entail_conjunct,Trace
imply_raw,Trace

Command:
../sleek ex21e2-heap-node.slk -debug dd.log >1


Command:
../sleek ex25-test-err.slk --dd-calls-all -dre ".*imply" > 1


DEBUGGED CALLS
==============
9
(eq_spec_var,140)
(get_hash2,24)
(can_be_aliased_aux,20)
(smt_of_formula,16)
(h_fv,15)
(isAnyConstFalse,14)
(eqExp_f,11)
(get_concrete_bag_pure,10)
(mix_of_pure,10)

%%%                     imply_timeout 3@5.
%%%                      imply_timeout 2@6.
%%%                       elim_exists
%%%                        elim_exists
%%%                       elim_exists
%%%                        elim_exists
%%%                       imply_label_filter@7.
%%%                       eqExp_f
%%%                        eq_spec_var
%%%                       eqExp_f
%%%                        eq_spec_var

