#!/bin/sh
for i in dd_no2.txt
do
    #echo $i
    sed -f mk-sed.sed $i 
done
