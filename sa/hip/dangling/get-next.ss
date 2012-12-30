data node {
	int val;
	node next
}

HeapPred H(node a).
HeapPred G(node a, node b).

/*
  requires x::node<_,q>
  ensures x'::node<_,null> & res=q;//'
*/

/* return the tail of a singly linked list */
node get_next(ref node x)
  infer[H,G]
  requires H(x)
  ensures G(x',res);//'
/*
[ H(x_540) ::= x_540::node<val_31_510',next_31_511'>@M * HP_526(next_31_511')&true,
 G(x_541,res_542) ::= HP_526(res_542) * x_541::node<val_31_533,next_32_514'>@M&next_32_514'=null]
*

--sa-dangling
*************************************
*******relational definition ********
*************************************
[ H(x_540) ::= x_540::node<val_31_510',next_31_511'>@M * HP_526(next_31_511')&true,
 G(x_541,res_542) ::= HP_526(res_542) * x_541::node<val_31_533,next_32_514'>@M&next_32_514'=null,
 HP_526(res) ::= emp&DLING_HP_526_res_543=res]
*

--sa-dangling --sa-inlining
[ H(x_540) ::= x_540::node<val_31_510',DLING_HP_526_res_543>@M&true,
 G(x_541,res_542) ::= x_541::node<val_31_533,next_32_514'>@M&next_32_514'=null & 
DLING_HP_526_res_543=res_542]
*

PROBLEM : printing inconsistent below..

*******relational definitions (wo elim-dangling) ********
[ H(x_540)::  x_540::node<val_31_510',next_31_511'>@M * HP_526(next_31_511')&true,
 G(x_541,res_542)::  HP_526(res_542) * x_541::node<val_31_533,next_32_514'>@M&next_32_514'=null]

*************************************
*******relational definition ********
*************************************
[ H(x_540) ::= x_540::node<val_49_510',next_49_511'>@M * HP_526(next_49_511')&true,
 G(x_541,res_542) ::= HP_526(res_542) * x_541::node<val_49_533,next_50_514'>@M&next_50_514'=null,
 HP_526(res) ::= emp&DLING_HP_526_res_543=res]
*
*************************************
*
*/
{
  node tmp = x.next;
  x.next = null;
  return tmp;
}

/*
From get-next, I would expect rel ass derived to be:

BIND
====
H(x)&true  --> x::node<val_20_510',next_20_511'> 
   * HP_526(next_20_511')&true

POST
=====
HP_526(res) * x'::node<_,null>
 --> G(x',res)&true

From these, we know that HP_526 is a dangling
predicate, and proceed to define it as:
        HP_526(n)= n=n#
where n# is a logical variable.

Normalization then leads to:

H(x) == x::node<_,n#>
G(x',res) == x'::node<_,null> & res=n#

where n# is a logical variable that links
between pre and post-condition

==================
ERROR with --sa-dangling
 HP_526 not properly eliminated..
 please print before and after such options.

[ H(x_540) ::= x_540::node<val_31_510',next_31_511'>@M * HP_526(next_31_511')&true,
 G(x_541,res_542) ::= HP_526(res_542) * x_541::node<val_31_533,next_32_514'>@M&next_32_514'=null,
 HP_526(res) ::= emp&DLING_HP_526_res_
*/

