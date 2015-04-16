#!/bin/sh
for i in *.ml
do
    echo $i
    ocp-indent $i > $i.tst
    #sed -i -f mv-var.sed $i 
done
