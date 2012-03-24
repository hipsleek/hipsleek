data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or self::node<v,q>*q::ll<n-1>
  inv n>=0;

/*
   (1) Write the strongest postcondition
   (2) Prove the algorithm terminates under the given precondition
*/

node insert(node x, node v)
  requires x::ll<n>*v::node<_,_> & Term[n]
  ensures res::ll<n+1> & (res=x | res=v);
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

