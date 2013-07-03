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
one set-tail-2.ss
one sll-dll.ss
one last-2.ss
one dll-append_paper.ss
one "zip_paper_leq.ss --sa-en-sp-split --pred-en-dangling"
one tll3.ss

