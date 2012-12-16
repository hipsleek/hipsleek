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

HeapPred H(node a).
HeapPred H1(node a).

HeapPred H2(node a).
HeapPred H3(node a).

//The number of elements that conform the list's content.
//relation SIZEH(int a, int b, int c).
int size_helper(node x, ref int n)
  infer[H,H1]
  requires H(x) //0<=m
     ensures  H1(x);// & SIZEH(res,n);//res=m+n & m>=0
{
  if (x==null) 
    return n;
  else {
    n = n+1;
    return size_helper(x.next, n);
  }
}

int size(node x)
   infer[H2,H3]
   requires H2(x) //0<=m
   ensures  H3(x);
  /* requires x::ll1<> */
  /* ensures true; */
{
  int n = 0;
  return size_helper(x, n);
}
