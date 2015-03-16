#!/bin/sh
for i in *.ml
do
    echo $i,###
    sed -n -f list-binfo.sed $i 
done
