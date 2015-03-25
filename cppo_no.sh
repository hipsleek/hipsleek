#!/bin/sh

./sh_proc  $1> $1".sed"
sed -i -f $1".sed" $1