data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

lldist<v,n> == self = null & n = 0 
  or self::node<v, q> * q::lldist<h,n-1> & v!=h
  inv n >= 0;

relation R(int n, int m).

node distinct(node x)
  requires x::ll<n>
  ensures res::lldist<_,m> & m<=n
  // R(res,n) = res=n
{
  if (x==null) return 0;
  else {
    node xn=x.next;
    if (xn==null) {
      return x;
    } else {
      int y=xn.val;
      if (x.val==y) {
        x.next = distinct(yn);
        return x
      } else {
        xn = distinct(xn);
        return xn;
      }
    }
  }
}

/*

 infer [n,R] x::ll<n>@L & x=null & res=0 |- R(res,n)
      ==> res=0 & n=0 --> R(res,n)

 infer [n,R] x::node<_,q>@L*q::ll<m>@L & x!=null & res=1+r & m=n-1
                   & R(r,m)  |- R(res,n)
      ==> res=1+r & n=1+m & R(r,m) --> R(res,n)

*/

