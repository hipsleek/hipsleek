#!/bin/bash

echo $0 $1 > /tmp/asd

if [ "$#" -ne 1 ]; then
  echo "Usage: $0 <goals file name>"
  exit 1
fi

cat $1 | prolog -q
