#!/bin/bash
if [ $# -eq 1 ]
then
    ./hip info-test/hip/$1.ss
else
    ./hip info-test/hip/$1.ss -p $2
fi
