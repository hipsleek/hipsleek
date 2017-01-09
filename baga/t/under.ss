data node {
  node next;
}

ll<n> == self=null & n=0
  or self::node<q> * q::ll<n-1>
  inv_sat BG([],self=null&n=0) | BG([self],n=1) | BG([self],n=2) | BG([self],n=4)
  /* inv_exact BG([],self=null & n=0) | BG([self],n>0) */
  /* inv_sat BG([],self=null & n=0) | BG([self],n>0) */
  ;

  int foo()
requires true
    ensures true;
{
  return 1;
}
