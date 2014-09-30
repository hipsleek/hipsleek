/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next;
}

/* view for a singly linked list */
/* ll<n> == self = null & n = 0 */
/* 	or self::node<_, q> * q::ll<n-1> */
/*   inv n >= 0; */

HeapPred H1(node a).
HeapPred H2(node a).

HeapPred G1(node a).
HeapPred G2(node a).

//The number of elements that conform the list's content.
//relation SIZEH(int a, int b, int c).
int size_helper(node x, ref int n)
  infer[H1,G1]
  requires H1(x) //0<=m
  ensures G1(x);// & SIZEH(res,n);//res=m+n & m>=0
/*
{
  if (x==null) 
    return n;
  else {
    n = n+1;
    return size_helper(x.next, n);
  }
}
*/

int size(node x)
  infer[H1,H2,G1,G2]
   requires H2(x) //0<=m
   ensures  G2(x);
  /* requires x::ll1<> */
  /* ensures true; */
{
  int n = 0;
  return size_helper(x, n) + size(x.next);
}
