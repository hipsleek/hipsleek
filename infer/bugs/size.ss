data node {
	int val;
	node next;
}

ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

relation SIZEH(int a, int b, int c).
int size_helper(node x, ref int n)
  infer[SIZEH]
  requires x::ll<m> //0<=m
  ensures  SIZEH(res,m,n);//res=m+n & m>=0
{
  if (x==null) return n;
  else {
    n = n+ 1;
    return size_helper(x.next, n);
  }
}
relation SIZE(int a, int b).
int size(node x)
  infer[SIZE]
  requires x::ll<n> //0<=n
  ensures SIZE(res,n);//n>=0 & n=res
{
  int m = 0;
  return size_helper(x, m);
}
