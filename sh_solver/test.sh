#!/bin/bash
for file in tests/*
do
   echo ${file}
  ./exec.sh ${file}
done
