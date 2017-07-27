#!/bin/bash
for i in `seq 1 10`;
do
	../../../arr_test random${i}.slk 10
	../../../sleek random${i}.slk 
done

