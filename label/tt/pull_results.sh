#!/bin/bash

function one 
{
	sll_out=`../../hip --en-texify $1`
	rels=`echo "$sll_out" | awk '/rstart/,/rstop/'`
	defs=`echo "$sll_out" | awk '/dstart/,/dstop/'`
	echo "========$1=========="
	echo "$rels"
	echo "$defs"
	echo "===================="
}
one "set-tail-2.ss --pred-en-dangling $1"
one "sll-dll.ss --pred-en-dangling $1"
one "last-2.ss --pred-en-dangling $1"
one "dll-append_paper.ss --pred-en-dangling --classic $1"
one "zip_paper_leq.ss --sa-en-sp-split --pred-en-dangling $1"
one "tll.ss --sa-dnc --pred-en-dangling $1"

