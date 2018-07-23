#!/bin/bash
if [ $# -eq 0 ]
then
    ./hip info-test/eximdpr/double_if.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximdpr/double_if_precise.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximdpr/lemma.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximdpr/ll_length.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximdpr/ll_concat.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximdpr/ll_sum.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximdpr/pred_id.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximdpr/pred_cast.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximdpr/pred_unfold.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"

    ./hip info-test/eximdpr/mutual_exclusive.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"
    ./hip info-test/eximdpr/equal_branches.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma"

else
    ./hip info-test/eximdpr/double_if.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" > $1
    ./hip info-test/eximdpr/double_if_precise.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/eximdpr/lemma.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/eximdpr/ll_length.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/eximdpr/ll_concat.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/eximdpr/ll_sum.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/eximdpr/pred_id.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/eximdpr/pred_cast.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/eximdpr/pred_unfold.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1

    ./hip info-test/eximdpr/mutual_exclusive.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
    ./hip info-test/eximdpr/equal_branches.ss | grep "Procedure\|Stop\|Total verification\|Time spent\|Z3 Prover\|lemma" >> $1
fi
