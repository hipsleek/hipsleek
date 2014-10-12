data node {
  node next;
}

ll<n> == self=null & n=0
  or self::node<q> * q::ll<n-1>
  //inv_sat BG([],self=null & n=0)
  //inv_sat BG([self],true)
  //inv_sat BG([self],n>=0)
  inv_sat BG([self],n>0)
  ;
