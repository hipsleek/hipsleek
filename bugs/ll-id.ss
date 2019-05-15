data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

relation A(int n, int m, int z).
relation BBB(int n).

void id(node x, node y)
  infer [BBB]
  requires x::ll<nxnxnxn>*y::ll<m> & BBB(nxnxnxn)
  ensures x::ll<z>;
{
  if (x.next==null) {
    x = x;
  }
}
