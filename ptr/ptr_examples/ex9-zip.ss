data node {
  int val;
  node next;
}

ll<n> == self=null & n=0 
  or self::node<_,q>*q::ll<n-1>
inv n>=0;

relation P(int a,int b).
relation Q(int a,int b, int c).

node zip(node x,node y)
/*
 requires x::ll<a>*y::ll<b> & a=b
 ensures res::ll<n> & n=a;
*/
 infer[P,Q]
 requires x::ll<a>*y::ll<b> & P(a,b)
 ensures res::ll<n> & Q(a,b,n);
{
  if (x==null) return x;
  else {
    node r = new node(x.val+y.val,null);
    r.next = zip(x.next,y.next);
    return r;
  }
}
