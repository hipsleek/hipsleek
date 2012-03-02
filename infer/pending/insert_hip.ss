data node3 { 
  int val; 
  node3 left; 
  node3 right; 
}

//bt<n,h,s> == self=null & n=0 & h=0 & s=0 or self::node3<_,p,q> * p::bt<np,hp,sp> * q::bt<nq,hq,sq> & n=1+np+nq & h=1+max(hp,hq) & s=1+min(sp,sq) inv n>=0 & h>=0 & s>=0;

bt<n,h> == self=null & n=0 & h=0 
  or self::node3<_,p,q> * p::bt<np,hp> * q::bt<nq,hq> & n=1+np+nq & h=1+max(hp,hq) 
  inv n>=0 & h>=0;

relation A(int a, int b, int c, int d).

void insert(node3 x)
  infer [A,n,h]
  requires x::bt<n,h> 
  ensures x::bt<m,k> & A(n,h,m,k);
{
  node3 a, b;
  if (x.left == null)
    x.left = new node3(0,null,null);
  else {
    if (x.right == null)
      x.right = new node3(0,null,null);
    else {
      if (a == b) insert(x.left);
      else insert(x.right);
    }
  }
}

