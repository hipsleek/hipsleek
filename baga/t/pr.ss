data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or self::node<_, q> * q::ll<n-1>
  //inv n>=0
  //inv BG([],n>=0) 
  //inv BG([],self=null & n=0) | BG([self],n>0)
  inv_exact BG([],self=null & n=0) | BG([self],n>0)
  /* inv_sat BG([],self=null & n=0) | BG([self],n>0) */
  // under
  ;

void foo(node x) 
  requires x::ll<4+6>
  ensures true;
{
  dprint;
}


