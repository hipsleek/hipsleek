data node {
  node next;
}

ll<n> == self=null & n=0
  or self::node<q> * q::ll<n-1>
  //inv_sat BG([self],n>4)         // Not OK
  //inv_sat BG([],self=null) //& n=0) // OK
  // inv_sat BG([self],true)        // OK
  // inv_sat BG([self],n>=0)        // OK
  // inv_sat BG([self],n>0)         // OK
  // inv_sat BG([self],n=1)         // OK
  inv_sat BG([self],n>=2)        // OK
  //inv_sat BG([self],n>1)         // OK
   ;

/*
# ll-3d.ss

This works!

 */
