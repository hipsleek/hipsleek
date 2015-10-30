#!/bin/bash

# To replace by an expected output
expectedOutput="TERMINATION INFERENCE"

echo "Compiling $HG_NODE ..."
make >/dev/null 2>&1

echo "Running test ..."
# To replace by a test command
./hip -infer "@term"  /home/chanhle/tools/termCOMP15/TPDB/C/AProVE_numeric/Avg_true.c > tempResult 2>&1

if [ "$?" != 0 ]; then 
  echo "Unexpected Error"
  exit 1; 
fi # BAD
if grep -q "$expectedOutput" tempResult; then 
  echo "Found $expectedOutput --> GOOD"
  exit 0; # GOOD
else 
  echo "Not found $expectedOutput --> BAD"
  exit 1; # BAD
fi
