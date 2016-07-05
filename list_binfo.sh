#!/bin/sh
for i in *.ml
do
    if [ "$i" != "cilparser.ml" ]; then
        echo $i,###
        sed -i -f mv-binfo.sed $i
    fi
done
