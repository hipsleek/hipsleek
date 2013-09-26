data node{
 int val;
 node next;
}

ll<n,a> == self=null & n=0 or
  self::node<_@a,q>*q::ll<n-1,a>
  inv n>=0;

int length(node p)
/*
  requires p::ll<n,@M>
  ensures p::ll<n,@M> & res=n;
  requires p::ll<n,@A>
  ensures p::ll<n,@A> & res=n;
  requires p::ll<n,@L>
  ensures p::ll<n,@L> & res=n;
 // should flag an error here!
*/
  requires p::ll<n,@L>
  ensures p::ll<n,@A> & res=n;
{
  if (p==null) return 0;
    else return 1+length(p.next);
}

