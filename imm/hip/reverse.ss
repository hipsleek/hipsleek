data node{
 int val;
 node next;
}

ll<n,a1,a2> == self=null & n=0 or
  self::node<_@a1,q@a2>*q::ll<n-1,a1,a2>
  inv n>=0;

node reverse(node p)
  requires p::ll<n,@A,@M> 
  ensures  res::ll<n,@A,@M>; 

{
  if (p==null) return p;
  else if (p.next == null) 
    
    else return 1+length(p.next);
}
