#!/bin/sh
for i in *.ml
do
    echo $i
    sed -f tmp.sed $i 
done
