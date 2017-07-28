#!/bin/bash
for i in `seq 1 10`;
do
	../../../arr_test random_${i}_invalid.slk 10 Fail
	../../../sleek random_${i}_invalid.slk 
done

