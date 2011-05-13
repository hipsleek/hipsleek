#!/bin/sh
for i in $*
do
    sed -i -f rm-ho.sed $1 
done
