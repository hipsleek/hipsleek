data node {
  int val;
  node next;
}

lseg<p,n> == self=p & n=0
  or self::node<v,q>*q::lseg<p,n-1>
  inv n>=0;

clist<n> == self::node<s,q>*q::lseg<self,n-1> 
  inv n>=1;

lemma self::clist<n> <- self::lseg<q,n-1>*q::node<_,self>;

/* 
  (1) specify the precondition for non-termination
  (2) why is a lemma required?
      At the recursive call, we have:
         x::node<_,q>*q::lseg<x,n-1>
      but we have precondition:
         q::clist<n>
      To prove that we need to ensure:
          x::node<_,q>*q::lseg<x,n-1> |- q::clist<n>
      that is enabled by the lemma.
*/

int length(node x)
  requires x::clist<n> & Loop
  ensures false;
{
  if (x==null) {
       return 0;
  } else {
       int v = length(x.next);
       return 1+v;
  }
}


