data node {
  int val;
  node next;
}

ll<n> == emp & self=null & n=0
  or self::node<_,q>*q::ll<n-1>
  inv n>=0;

int length(node x)
//infer[@shape,@post_n,@term]
  infer[@post_n,@term]
  requires x::ll<n> 
  ensures x::ll<m>;
{
  if (x==null) return 0;
  else return 1+length(x.next);
}

