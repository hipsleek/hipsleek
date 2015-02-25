#!/bin/bash
# you can add to this script the same arguments that you would add to run-fast-tests.pl

echo -e "\n##################### compile #######################"
cd ../../ && make && cd examples/working

echo -e "\n##################### info ##########################"
hg log -l 1 -b . --template "Author: {author}\nBranch: {branch}\n"

echo -e "\n##################### sleek tests ###################"
time ./run-fast-tests.pl sleek $@
# imm1.slk and imm3.slk fail due to omitted base_case_fold

# soundness check for --eps
echo -e "\n##################### hip tests --eps #####################"
time ./run-fast-tests.pl hip -flags "--eps" $@