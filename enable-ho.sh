#!/bin/sh
for i in $*
do
    sed -i -f enable-ho.sed $1 
done
