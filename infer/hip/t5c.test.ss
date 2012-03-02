data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

int hd(node x)
// infer [x] 
  requires x::ll<n> & x!=null
 ensures x::node<a,b> * b::ll<m> & n=m+1 & res=a; 
/*
   requires x::node<inf1,in>
   ensures res=inf1;
*/
{
  return x.val;
}

int hdtl(ref node x)
// infer [x] 
 requires x::node<a,b> * b::ll<m> & b!=null
 ensures x'::node<c,d> * d::ll<e> & res=c & e=m-1; 
{
  x = tl(x);
  return hd(x);
}

node tl(node x)
// infer [x] 
 requires x::node<c,d>
 ensures res=d; 
{
  node t = x.next;
  return t;
}

