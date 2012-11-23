data node2 {
	int val;
	node2 prev;
	node2 next;
}

dll<p,n> == self = null & n = 0
  or self::node2<_ ,p , q> * q::dll<self, n-1> // = q1
	inv n >= 0;

HeapPred G1(node2 a).
HeapPred H1(node2 a).

void insert(node2 x, int a)
  /* infer[n] */
  /* requires x::dll<p, n> //& n>0 //&  x!=null */
  /* ensures x::dll<p, m> & m>n; */

  infer[H1,G1]
  requires H1(x)
  ensures G1(x);
{
  bool l = x.next == null;
  if (l)
    x.next = new node2(a, x, null);
  else
    insert(x.next, a);
}
