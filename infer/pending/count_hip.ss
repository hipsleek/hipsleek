data node3 { 
  int val; 
  node3 left; 
  node3 right; 
}

bt<n,h,s> == self=null & n=0 & h=0 & s=0 
  or self::node3<_,p,q> * p::bt<np,hp,sp> * q::bt<nq,hq,sq> & n=1+np+nq & h=1+max(hp,hq) & s=1+min(sp,sq) 
  inv n>=0 & h>=0 & s>=0;

relation A(int a, int b, int c, int d, int e, int f).

int count(node3 x)
  infer [A]
  requires x::bt<n,h,s>
  ensures x::bt<m,k,t> & A(m,n,k,h,t,s);
{
  if (x == null) return 0;
  else return 1 + count(x.left) + count(x.right);
}

