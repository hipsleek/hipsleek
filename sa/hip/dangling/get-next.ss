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
[ H(x)&true --> x::node<val_20_510',next_20_511'> * HP_526(next_20_511')&true,
 HP_526(next_21_534) * x'::node<val_20_533,next_21_514'>&
  next_21_514'=null --> G(x',next_21_534)&true]

  // WHY didn't we preserve "res", as captured below:

 checkentail HP_526(next_28_534) * x'::node<val_27_533,next_28_514'>@M[Orig]&x=x' & 
next_28_514'=null & next_28_534=v_node_29_515' & res=v_node_29_515'&
{FLOW,(22,23)=__norm}[]
 |-  G(x',res)&true&{FLOW,(22,23)=__norm}[]. 

ass hprel: [ HP_526(res) * x'::node<val_27_533,next_28_514'>&
  next_28_514'=null --> G(x',res)&true]
  ]
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
