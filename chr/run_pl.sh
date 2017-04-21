#!/bin/bash
# Usage example: ./run_pl.sh session_chr_prelude /tmp/test

if [ "$#" -ne 2 ]; then
  echo "Usage: $0 <prolog script name> <goals file name>"
  exit 1
fi

PL_FILE=$1
PL_FILE="${PL_FILE%.*}"

echo -en "[$PL_FILE]." $(cat $2) | prolog -q
