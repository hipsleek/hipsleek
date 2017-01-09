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
//HeapPred G(node a, node b).
HeapPred G(node a).


//The number of elements that conform the list's content.
//relation SIZEH(int a, int b, int c).
int size_helper(node x, ref int n)
  infer[H,G]
  requires H(x) //0<=m
  ensures  G(x);// & SIZEH(res,n);//res=m+n & m>=0
{
  if (x==null) 
    return n;
  else {
    n = n+1;
    return size_helper(x.next, n);
  }
}
