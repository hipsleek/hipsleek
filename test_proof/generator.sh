#!/bin/bash

i="1"

while [ $i -lt 40 ]
do
echo $i 
./runz3 -gent $i 
#-boogie
i=$[$i+1] 
done
