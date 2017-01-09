data node {
  node next;
}

ll<n> == self=null & n=0
  or self::node<q> * q::ll<n-1>
   inv_sat BG([self],n>4)         // Not OK
 // inv_sat BG([],self=null & n=0) // OK
  // inv_sat BG([self],true)        // OK
  // inv_sat BG([self],n>=0)        // OK
  // inv_sat BG([self],n>0)         // OK
  // inv_sat BG([self],n=1)         // OK
  // inv_sat BG([self],n>=1)        // OK
  // inv_sat BG([self],n>1)         // OK
   ;

/*
# ll-3.ss

ll<n> == self=null & n=0
  or self::node<q> * q::ll<n-1>
   inv_sat BG([self],n>4)         // Not OK

should a sound under approx.

WARNING: t/ll-3.ss_5:9_5:24:view defn for ll has incorrectly supplied invariant
-- incorrect under-approx inv : Some([([self], 4<n)])


Did we unfold 4 times which allowed it to succeed
for ll-3e.ss but fails for ll-3.ss.

# ll-3e.ss

 inv_sat BG([self],n>=3)        // OK

This works!


 */
