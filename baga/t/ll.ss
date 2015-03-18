data node {
  node next;
}

data node2 {
  node2 prev;
  node2 next;
}

data node3 {
  int val;
  node3 next;
}

ll<n> == self=null & n=0
  or self::node<q> * q::ll<n-1>
  // inv_sat BG([],self=null & n=0) // OK
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
  // inv_sat BG([],self=null & n=0) // OK
  // inv_sat BG([self],n=1)         // OK
  // inv_sat BG([self],n=2)         // OK
  // inv_sat BG([self],true)        // OK
  // inv_sat BG([self],n>0)         // OK
  // inv_sat BG([self],n>=0)        // OK
  // inv_sat BG([self],n=4)         // OK
  ;

oll<n> == exists q: self::node<q> & q=null & n=1
  or exists p,q: self::node<q> * q::node<p> * p::oll<n-2>
  ;

dll<p,n> == self=null & n=0
  or exists q: self::node2<p,q> * q::dll<self,n-1>
  ;

sll<n,mn,mx> == self=null & n=0 & mn<=mx
  or exists v,q: self::node3<v,q> * q::sll<n-1,v,mx> & mn<=v & v<=mx
  ;

lseg<p,n> == self=p & n=0
  or exists q: self::node<q> * q::lseg<p,n-1>
  ;
