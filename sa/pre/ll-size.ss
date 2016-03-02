/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next;
}

/* view for a singly linked list */
ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

HeapPred H(node a).

int size_helper(node x)
  infer[H]
  requires H(x)   ensures true;
{
  if (x==null) 
    return 0;
  else {
    return 1+size_helper(x.next);
  }
}

/*
// abduction

*************************************
*******shape relational assumptions ********
*************************************
[ // BIND
(2;0)H(x)&x!=null --> x::node<val_23_1494,next_23_1495> * 
HP_1496(next_23_1495)&
true,
 // PRE_REC
(2;0)HP_1496(next_23_1495)&true --> H(next_23_1495)&
true]

// coverage path wrt. base case, avoid dead code
H(x) & x=null --> true
==> //x=null => emp heap
H(x) & x=null --> emp&true

 */

