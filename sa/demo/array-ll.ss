data node {
  int val;
  node next;
}

ll<> == self=null
	or self::node<_, q> * q::ll<> & self!=null
	inv true;
relation dom(node[] a, int x, int y) == true.

void foo( node [] a, node p)
  requires dom(a, 0, 3)
    ensures  dom(a, 0, 3) & a[0] = p;
{
  a[0]=p;
}

