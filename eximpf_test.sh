#!/bin/bash
if [ $# -eq 0 ]
then
    ./hip info-test/eximpf/double_if.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximpf/double_if_precise.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximpf/lemma.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximpf/ll_length.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximpf/ll_concat.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximpf/ll_sum.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximpf/pred_id.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximpf/pred_cast.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximpf/pred_unfold.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"

    ./hip info-test/eximpf/mutual_exclusive.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"

else
    ./hip info-test/eximpf/double_if.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" > $1
    ./hip info-test/eximpf/double_if_precise.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/eximpf/lemma.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/eximpf/ll_length.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/eximpf/ll_concat.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/eximpf/ll_sum.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/eximpf/pred_id.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/eximpf/pred_cast.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/eximpf/pred_unfold.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1

    ./hip info-test/eximpf/mutual_exclusive.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
fi
