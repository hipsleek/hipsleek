data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

relation R(int n, int m).

int length(node x)
  infer [R]
  requires x::ll<n>@L
  ensures R(res,n);
  // R(res,n) = res=n
{
  if (x==null) return 0;
  else {
    int r = length(x.next);
    return 1+r;
  }
}

/*

 infer [n,R] x::ll<n>@L & x=null & res=0 |- R(res,n)
      ==> res=0 & n=0 --> R(res,n)

 infer [n,R] x::node<_,q>@L*q::ll<m>@L & x!=null & res=1+r & m=n-1
                   & R(r,m)  |- R(res,n)
      ==> res=1+r & n=1+m & R(r,m) --> R(res,n)

*/

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

relation A(int n, int m, int z).

void append(node x, node y)
  infer [n,A]
  requires x::ll<n>*y::ll<m> 
  ensures x::ll<z> & A(n,m,z);
{
  if (x.next==null) {
    x.next=y; 
  } else {
    append(x.next,y);
  }
}
