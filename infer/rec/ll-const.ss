data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;


relation F(int n, int m).

int foo(node x)
  infer [F]
  requires x::ll<n>@L
  ensures F(res,n);  
  // R(res,n) = res=0
{
  if (x==null) return 0;
  else {
    int m = foo(x.next);
    return m;
  }
}

