/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}

/*
HeapPred H(node a).
HeapPred H1(node a).
HeapPred H2(node a, node b).
  HeapPred H3(node a, node b, node c).
HeapPred G(node a, node b).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node a, node b, node c).
*/

ls<y> == self=y
  or self::node<_,q>*q::ls<y> & self!=y
inv true;

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

void append(ref node x, node y)
//infer [H2,G3]
//requires H2(x,y)
//ensures G3(x,x',y); //'
//requires x::ls<null>*y::ls<null> 
//ensures x'::ls<null>; //'
requires x::ll<n> * y::ll<m>
ensures x'::ll<n+m>; //'
{
    if (x==null) { 
        x = y;
    }
	else {
       append(x.next, y);
    }
}
