#!/bin/bash
if [ $# -eq 0 ]
then
    ./hip info-test/hip/double_if.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/hip/double_if_precise.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/hip/lemma.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/hip/ll_length.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/hip/ll_concat.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/hip/ll_sum.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/hip/pred_id.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/hip/pred_cast.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/hip/pred_unfold.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"

    ./hip info-test/hip/mutual_exclusive.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"

else
    ./hip info-test/hip/double_if.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" > $1
    ./hip info-test/hip/double_if_precise.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/hip/lemma.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/hip/ll_length.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/hip/ll_concat.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/hip/ll_sum.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/hip/pred_id.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/hip/pred_cast.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/hip/pred_unfold.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1

    ./hip info-test/hip/mutual_exclusive.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
fi
