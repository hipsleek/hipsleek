#!/bin/bash
# you can add to this script the same arguments that you would add to run-fast-tests.pl

echo -e "\n##################### hip tests #####################"
./run-fast-tests.pl hip $@

echo -e "\n##################### sleek tests ###################"
./run-fast-tests.pl sleek $@

echo -e "\n##################### bags tests (runs with -tp mona) #####################"
./run-fast-tests.pl bags $@ -tp mona

echo -e "\n##################### term tests #####################"
./run-fast-tests.pl term $@

echo -e "\n##################### lists tests #####################"
./run-fast-tests.pl lists $@ -tp coq


