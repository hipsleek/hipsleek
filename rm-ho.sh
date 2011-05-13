#!/bin/sh
#sed -i .bak -f rm-ho.sed $1 && rm $1.bak 
sed -n -f rm-ho2.sed $1 
