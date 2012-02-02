/*
use --term-verbose 0

TODO:
 (i) inadequate message for unbounded measures
 (ii) missing message for valid bounded measure 

Termination checking result:
(18) (ERR: not bounded) 

(19)->(24) (OK) Term[0; (0 - 3)+(2*n)] -> Term[0; (0 - 3)+(2*n_651)+1]: Current context
heap: x'::node<Anon_636,q_637>@M[Orig]
pure: flted_7_635+1=n & x'=x & y'=y & x!=null & q_637!=null & 
      207::!(v_bool_21_517') & q_637!=null & !(v_bool_21_517') & 
      v_node_24_516'=q_637 & n_651=flted_7_635 & m_652=m
*/



data node {
  int val;
  node next;
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

void append(node x, node y)
  requires x::ll<n>*y::ll<m> & n>0 & Term[-3+2*n+1]
  ensures x::ll<z> & z=m+n;
{
  app2(x,y);
}

void app2(node x, node y)
  requires x::ll<n>*y::ll<m> & x!=null & Term[-3+2*n]
  ensures x::ll<z> & z=m+n;
{
  if (x.next==null) {
    x.next=y; 
  } else {
    append(x.next,y);
  }
}
