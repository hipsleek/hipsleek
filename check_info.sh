#!/bin/bash
proc_fs="Procedure [a-zA-Z0-9_]*fail[$][a-zA-Z0-9_]* SUCCESS"
proc_sf="Procedure [a-zA-Z0-9_]*safe[$][a-zA-Z0-9_]* FAIL"
lemma_fs="Entailing lemma [a-zA-Z0-9_>-]*fail[:] Valid"
lemma_sf="Entailing lemma [a-zA-Z0-9_>-]*safe[:] Fail"
sh info_test.sh > $1
if [ $# -eq 1 ]
then
  while read -r line;
  do
    if [[ $line =~ $proc_fs ]];
    then
      echo $line " :: (-)"
    fi

    if [[ $line =~ $proc_sf ]];
    then
      echo $line " :: (+)"
    fi

    if [[ $line =~ $lemma_fs ]];
    then
        echo $line " :: (-)"
    fi

    if [[ $line =~ $lemma_sf ]];
    then
        echo $line " :: (+)"
    fi
  done < "$1"
fi
