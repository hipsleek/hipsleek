data node {
  int val;
  node next;
}

lsort<s,n> == self::node<s,null> & n=1
  or self::node<s,q>*q::lsort<s2,n-1> & s<=s2 
  inv n>=1;

/*
   (1) Write the strongest postcondition
   (2) Prove termination of this algorithm for given spec

*/

node insert(node x, node v)
  requires v::node<a,_>
  case {
    x=null ->  
      requires true
      ensures res::lsort<a,1>;
    x!=null -> 
      requires x::lsort<h,n> 
      ensures res::lsort<min(a,h),n+1>;
  }
{
  if (x==null) {
       v.next=null;
       return v;
  } else {
       if (v.val<=x.val) {
           v.next = x;
           return v;
       } else {
         //assume false;
          node r = insert(x.next, v);
          x.next = r;
          return x;
       }
  }
}

