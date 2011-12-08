#!/bin/bash

rm pomega_*.res
rm pmona_*.res

for i in $( ls pomega/*.ss ); do
	echo $i

	echo Run $i with Automatic Slicing
	echo $i >> pomega_as.res
	../../../hip --eps $i >> pomega_as.res

	echo Run $i with No Slicing
	echo $i >> pomega_ns.res
	../../../hip --eps --force_one_slice_proving --force_one_slice $i >> pomega_ns.res
done

for i in $( ls pmona/*.ss ); do
	echo $i

	echo Run $i with Automatic Slicing
	echo $i >> pmona_as.res
	../../../hip -tp mona --eps $i >> pmona_as.res

	echo Run $i with No Slicing
	echo $i >> pmona_ns.res
	../../../hip -tp mona --eps --force_one_slice_proving --force_one_slice $i >> pmona_ns.res
done