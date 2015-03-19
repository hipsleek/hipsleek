data node3 { 
  int val; 
  node3 left; 
  node3 right; 
}

bt<n,h,s> == self=null & n=0 & h=0 & s=0 
  or self::node3<_,p,q> * p::bt<np,hp,sp> * q::bt<nq,hq,sq> & n=1+np+nq & h=1+max(hp,hq) & s=1+min(sp,sq) 
  inv n>=0 & h>=0 & s>=0;

relation A(int x, int y, int z, int t, int u, int v).

void trav_1(node3 x)
  infer [n,h,s,A]
  requires x::bt<n,h,s>
  ensures x::bt<m,w,t> & A(n,m,h,w,s,t);
{
  if (x != null) {
    trav_1(x.left);
    trav_1(x.right);
  } 
}


