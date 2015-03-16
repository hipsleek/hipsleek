#!/bin/sh
for i in *.ml
do
    echo $i
    sed -i -f mv-var.sed $i 
done
