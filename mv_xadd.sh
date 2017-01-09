#!/bin/sh
for i in *.ml
do
    echo $i
    sed -i -f mv-xadd.sed $i 
done
