#!/bin/bash
# you can add to this script the same arguments that you would add to run-fast-tests.pl

# fixed in infer2r_lbl at moment
#echo -e "\n##################### term tests #####################"
#time ./run-fast-tests.pl term $@
# some failures ex1.ss, ex12, ex12b, ex12c

echo -e "\n##################### sleek tests ###################"
time ./run-fast-tests.pl sleek $@
# imm1.slk and imm3.slk fail due to omitted base_case_fold

# another check for lemma-proving

# soundness check for --eps
echo -e "\n##################### hip tests --eps #####################"
time ./run-fast-tests.pl hip -flags "--eps" $@

echo -e "\n##################### imm tests --eps ###################"
time ./run-fast-tests.pl imm -flags "--eps" $@ -tp redlog

# fixed in infer2r_lbl at moment
#echo -e "\n##################### lists tests #####################"
#time ./run-fast-tests.pl lists $@ -tp coq
# takes a long time for lr.ss!


# soundness check for no eps
echo -e "\n##################### imm tests --eps ###################"
time ./run-fast-tests.pl imm $@ -tp redlog


echo -e "\n##################### bags tests (runs with -tp mona) ###very slow!##################"

time ./run-fast-tests.pl bags -flags "--eps" $@ -tp mona


