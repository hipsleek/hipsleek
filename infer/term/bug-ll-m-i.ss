data node {
  int val;
  node next;
}

ranking r1(int n).
ranking r2(int n).

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

void append(node x, node y)
  infer [r1,r2]
  requires x::ll<n>*y::ll<m> & n>0 & Term[r1(n)]
  ensures x::ll<z> & z=m+n;
{
  app2(x,y);
}

void app2(node x, node y)
  infer [r1,r2]
  requires x::ll<n>*y::ll<m> & x!=null & Term[r2(n)]
  ensures x::ll<z> & z=m+n;
{
  if (x.next==null) {
    x.next=y; 
  } else {
    append(x.next,y);
  }
}


/*
(24)->(29) (OK: decreasing) Term[0; r2(n)] -> Term[0; r1(n_637)]:
Current context
heap: x'::node<Anon_622,q_623>@M[Orig]
pure: flted_10_621+1=n & x'=x & y'=y & x!=null & q_623!=null & 
      209::!(v_bool_26_514') & q_623!=null & !(v_bool_26_514') & 
      v_node_29_513'=q_623 & n_637=flted_10_621 & m_638=m
(23) (OK: bounded):
Current context
heap: x::ll<n>@M[Orig][LHSCase] * y::ll<m>@M[Orig][LHSCase]
pure: x'=x & y'=y & x!=null
(16)->(18) (OK: decreasing) Term[0; r1(n)] -> Term[0; r2(n_590)]:
Current context
pure: x'=x & y'=y & 0<n & n_590=n & m_591=m
(15) (OK: bounded):
Current context
heap: x::ll<n>@M[Orig][LHSCase] * y::ll<m>@M[Orig][LHSCase]
pure: x'=x & y'=y & 0<n
*/

/*
TODO : One decreasing relation is missing in INFERENCE: WHY?
!!! NEW RANK:[ ( 1<=n) -->  (r1(n))>=0, ( n=n_590 & 1<=n_590) -->  (r1(n))>(r2(n
_590))]
!!! NEW RANK:[ ( 1<=n) -->  (r2(n))>=0]
*/
