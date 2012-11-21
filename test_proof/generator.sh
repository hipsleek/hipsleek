#!/bin/bash

i="1"

while [ $i -lt 60 ]
do
echo $i 
./runz3 -gent $i -boogie -imp
./runz3 -gent $i -frama-c
./runz3 -gent $i -frama-c -imp 
i=$[$i+1] 
done
