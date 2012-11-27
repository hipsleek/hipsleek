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
[ H(x)&true --> x::node<val_28_510',next_28_511'> * HP_523(next_28_511')&true,
 HP_523(res) * x'::node<val_28_527,res>&true --> G(x',res)&true]
*************************************

*************************************
*******relational definition ********
*************************************
[ H(x_530) ::= x_530::node<val_28_510',HP_523_res_533>&true,
 G(x_531,res_532) ::= x_531::node<val_28_527,res_532>&HP_523_res_533=res_532]
*/
{
  node tmp = x.next;
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

*/
