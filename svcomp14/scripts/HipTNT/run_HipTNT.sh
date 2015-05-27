#!/bin/bash

SVC_PATH=/home/chanhle/tools/svcomp15/benchmarks/
BENCH=$SVC_PATH$1
out=out.txt
time=out.time.txt

for fc in $BENCH/*.c; do
  filename=$(basename "$fc")
  filename="${filename%.*}"

  printf "$filename\t"
  timeout 60 /usr/bin/time -f "%e" ./hiptnt_simpl $fc 1> $out 2> $time
  if [ $? -eq 124 ]; then
    printf "TIMEOUT"
  else
    read res < $out
    read runtime < $time
    printf "$res\t$runtime"
  fi
  printf "\n"
done;

