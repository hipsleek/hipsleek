#!/bin/bash
# you can add to this script the same arguments that you would add to run-fast-tests.pl


echo -e "\n##################### sleek tests ###################"
time ./run-fast-tests.pl sleek $@
# imm1.slk and imm3.slk fail due to omitted base_case_fold

echo -e "\n##################### sleek_fracperm tests ###################"
time ./run-fast-tests.pl sleek_fracperm $@

echo -e "\n##################### hip_vperm tests ###################"
time ./run-fast-tests.pl hip_vperm $@

echo -e "\n##################### parahip tests ###################"
time ./run-fast-tests.pl parahip $@

echo -e "\n##################### must-bugs error tests ###################"
time ./run-fast-tests.pl musterr $@

# soundness check for --eps
echo -e "\n##################### hip tests --eps #####################"
time ./run-fast-tests.pl hip -flags "--eps" $@

echo -e "\n##################### infinity tests ########################"
time ./run-fast-tests.pl infinity $@

echo -e "\n##################### imm tests --eps ###################"
time ./run-fast-tests.pl imm -flags "--eps" $@ -tp redlog

echo -e "\n##################### mem tests ######################"
time ./run-fast-tests.pl mem $@

# fixed
echo -e "\n##################### term tests #####################"
time ./run-fast-tests.pl term $@
# some failures ex1.ss, ex12, ex12b, ex12c

echo -e "\n##################### modular formulae tests #####################"
time ./run-fast-tests.pl hip_long_mod $@
# another check for lemma-proving
# problem to be fixed! many failures
echo -e "\n##################### lists tests #####################"
time ./run-fast-tests.pl lemmas $@ 

# problem to be fixed!
echo -e "\n##################### lists tests #####################"
time ./run-fast-tests.pl lists $@ -tp coq
# takes a long time for lr.ss!


echo -e "\n##################### NO slicing tests ?? ###################"
#time ./run-fast-tests.pl hip_slicing $@

# soundness check for no eps
echo -e "\n##################### imm tests no eps ###################"
time ./run-fast-tests.pl imm $@ -tp redlog



echo -e "\n##################### bags tests (runs with -tp mona) ###very slow!##################"

time ./run-fast-tests.pl bags -flags "--eps" $@ -tp mona

echo -e "\n##################### array tests (runs with -tp z3) #####################"

time ./run-fast-tests.pl array -flags "--eps" $@ -tp z3

