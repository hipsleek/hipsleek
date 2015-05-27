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

