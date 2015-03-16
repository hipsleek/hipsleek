data node {
	int val;
	node next
}

HeapPred H(node a).
HeapPred G(node a, node c, node b).

/*
  requires x::node<_,q>
  ensures x'::node<_,null> & res=q;//'
*/

/* return the tail of a singly linked list */
node get_next(ref node x)
  infer[H,G]
  requires H(x)
  ensures G(x',x,res);//'
            /*
Got:
ass hprel: [ HP_527(res) * x'::node<val_22_534,next_23_515'>&x=x' & 
  next_23_515'=null --> G(x',x,res)&true]
which differs from:

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

*/
