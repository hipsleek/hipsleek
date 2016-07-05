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

 H(x_542) ::= x_542::node<val_36_510',HP_526_res_549>&true,
 G(x',res) ::= x'::node<val_36_533,next_37_514'>&next_37_514'=null & HP_526_r es_549=res
*/
{
  node tmp = x.next;
  x.next = null;
  return x;
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

*/
