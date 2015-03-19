data node{
 int val;
 node next;
}

ll<n,a1,a2> == self=null & n=0 or
  self::node<_@a1,q@a2>*q::ll<n-1,a1,a2>
  inv n>=0;

lla<n> == self=null & n=0 or
  self::node<_,q>*q::lla<n-1>
  inv n>=0;

int length(node p)
  requires p::ll<n,@A,@L> 
  ensures p::ll<n,@M,@A> & res=n ; 

{
  if (p==null) return 0;
    else return 1+length(p.next);
}

int lengtha(node p)
  requires p::lla<n> 
  ensures p::lla<n> & res=n ; 

{
  if (p==null) return 0;
    else return 1+lengtha(p.next);
}

