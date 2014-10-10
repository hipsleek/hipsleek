/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next;
}

/* view for a singly linked list */
ll<> == self = null
	or self::node<_, q> * q::ll<>
  ;


lln<n> == self = null & n = 0
	or self::node<_, q> * q::lln<n-1>
  inv n >= 0;

HeapPred H(node a).
HeapPred G(node a).

//relation SIZEH(int a, int b, int c).

int size_helper(node x)

/*
  infer[H,G]
  requires H(x) //0<=m
  ensures  G(x);// & SIZEH(res,n);//res=m+n & m>=0
*/

infer[@shape]  requires true ensures true;

//infer[@shape@size]  requires true ensures true;
{
  if (x==null)
    return 0;
  else {
    return size_helper(x.next) + 1;
  }
}

