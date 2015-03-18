#!/bin/sh
for i in astsimp.ml
do
    echo $i
    sed -i -f mv-binfo.sed $i 
done
