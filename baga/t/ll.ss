data node {
  node next;
}

ll<n> == self=null & n=0
  or self::node<q> * q::ll<n-1>
   inv_sat BG([],self=null & n=0) // OK
  // inv_sat BG([self],true)        // OK
  // inv_sat BG([self],n>=0)        // OK
  // inv_sat BG([self],n>0)         // OK
  // inv_sat BG([self],n=1)         // OK
  // inv_sat BG([self],n>=1)        // OK
  // inv_sat BG([self],n>1)         // OK
  // inv_sat BG([self],n>4)         // Not OK
  // inv_sat BG([],false)           // OK
  // inv_sat BG([self],n<=0)        // OK
  // inv_sat BG([self],n=0)         // OK
  ;

ell<n> == self=null & n=0
  or exists p,q: self::node<q> * q::node<p> * p::ell<n-2>
   inv_sat BG([],self=null & n=0) // OK
  // inv_sat BG([self],n=1)         // OK
  // inv_sat BG([self],n=2)         // OK
  // inv_sat BG([self],true)        // OK
  // inv_sat BG([self],n>0)         // OK
  // inv_sat BG([self],n>=0)        // OK
  // inv_sat BG([self],n=4)         // OK
  ;
