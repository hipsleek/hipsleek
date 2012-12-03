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
[ H(x)&true --> x::node<val_36_510',next_36_511'> * HP_526(next_36_511')&true,
 HP_526(res) * x'::node<val_36_533,next_37_514'>&
  next_37_514'=null --> G(x',res)&true]

[ H(x_542) ::= x_542::node<val_28_510',next_28_511'>@M * HP_526(next_28_511')&true,
 G(x',res) ::= HP_537(res) * x'::node<val_28_533,next_29_514'>@M&next_29_514'=null,
 HP_526(res) ::= HP_537(res)&true]

ERROR : Why an extra HP_537?
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

