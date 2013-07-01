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
HeapPred H1(node a).
HeapPred H5(node a).
HeapPred G1(node a).

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

bool empty(node x)
  infer[H5,G1]
  requires H5(x)
     ensures G1(x) & res | !res;
  /* requires x::ll1<> */
  /* case { */
  /*   x = null -> ensures EMPT1(res);//res */
  /*   x != null -> ensures EMPT2(res);//!(res) */
  /* } */
{
  if (x == null)
    return true;
  else
    return false;
}
