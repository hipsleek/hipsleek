#!/bin/sh
for i in x-num.txt
do
    #echo $i
    sed -f mk-sed.sed $i 
done
