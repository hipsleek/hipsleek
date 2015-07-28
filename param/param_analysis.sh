#!/usr/bin/bash

# Need directory of this bash script, so we can refer to the awk script.
DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )

$DIR/../hip $1 -dre analyse_param | awk -f $DIR/filter_analysis.awk
