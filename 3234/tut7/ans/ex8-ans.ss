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
   Explain why the following non-termination specification
   failed. 
   Add an "assume false" to the branch where it was terminating.
*/

node insert(node x, node v)
  requires x::clist<n> * v::node<_,_> 
  ensures false;
{
  if (x==null) {
       v.next=null;
       return v;
  } else {
       if (v.val<=x.val) {
           v.next = x;
           return v;
       } else {
          node r = insert(x.next, v);
          x.next = r;
          return x;
       }
  }
}

