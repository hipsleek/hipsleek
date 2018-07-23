#!/bin/bash
if [ $# -eq 1 ]
then
    ./hip info-test/eximpf/$1.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
else
    ./hip info-test/eximpf/$1.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" > $2
fi
