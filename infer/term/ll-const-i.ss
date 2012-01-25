data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

ranking r1(int n).

int foo(node x)
  infer [r1]
  requires x::ll<n>@L & Term[r1(n)]
  ensures res=0;  
{
  if (x==null) return 0;
  else {
    int m = foo(x.next);
    return m;
  }
}

