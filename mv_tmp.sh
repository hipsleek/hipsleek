#!/bin/sh
for i in *.ml
do
    echo $i
    sed -i -f tmp.sed $i 
done
