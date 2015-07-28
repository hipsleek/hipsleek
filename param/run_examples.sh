#!/usr/bin/bash

# Need directory of this bash script, so we can refer to the awk script.
DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )

function run_example {
    filename=$1
    description=$2

    echo $description:
    echo $filename
    $DIR/param_analysis.sh $DIR/$filename
    echo
}

run_example "./ex21-param-analyse.ss"   "the basic example"
run_example "./ex21d-swapping-param.ss" "swap params"
run_example "./ex21k-param-analyse.ss"  "swap params (alt)"
run_example "./ex24b-constant.ss"       "const"
run_example "./ex24e-unrelated.ss"      "unrelated"
run_example "./ex31-exists-param.ss"    "increasing"
run_example "./ex31c-incplussome.ss"    "unknown (inc and dec)"
