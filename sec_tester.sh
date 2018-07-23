#!/bin/bash
./hip info-flow/hip/$1.ss --info_flow | grep --line-buffered "Procedure"
