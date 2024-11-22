#!/bin/sh

# Script to filter the output of hip.exe.
# It accepts a space-separated list of procedures that were verified,
# and outputs only the verification result. It also outputs a warning
# if it found less lines than expected in the output.

check_lines () {
  output_lines=0
  while read line; do
    output_lines=$(($output_lines+1))
    echo $line
  done
  if  [ $output_lines -lt $1 ]; then
    echo "[WARNING] Filtered output has less lines than expected (expecting $1, got $output_lines); check for errors from executable"
    return 1
  fi
}

test_count=$(echo "$@" | tr ' ' '\n' | sort | uniq | wc -l)
if [ $# -eq 0 ]; then
  test_count=0
fi

procedure_filter="($(echo "$@" | tr ' ' '|'))"

grep -E "^(Procedure|Entailing lemma) $procedure_filter\\\$" \
  | sed -E 's/Entailing lemma/Entailment/g' \
  | sed -E 's/\$([_a-zA-Z0-9]+(~[_a-zA-Z0-9]+)*)?//g' \
  | sed -E 's/\..*$//g' \
  | sort -k 2 | uniq \
  | check_lines $test_count

