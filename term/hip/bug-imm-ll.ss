/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


ls<n,p> == self = p & n = 0 
  or self::node<_, q> * q::ls<n-1,p> 
  inv n >= 0;

clist<n> == self::node<_,q>*q::ls<n-1,self>
  inv n>0;

lemma self::clist<n> <- self::ls<n-1,q>*q::node<_,self>;

/*
Verification Context:(Line:22,Col:10)
Proving precondition in method length$node for spec:
 EBase exists (Expl)(Impl)[Anon_583](ex)v_node_27_521'::clist<Anon_583>@L[Orig][LHSCase] &
       Loop & {FLOW,(20,21)=__norm}
         EAssume 1::
           false & false & {FLOW,(20,21)=__norm}
Current States: [ x'::node<Anon_578,q_579>@L[Orig] * q_579::ls<flted_15_577,self_576>@L[Orig] & flted_15_577+1=Anon_15 & self_576=x' & x'=x & x'!=null & 133::!(v_bool_24_525') & x'!=null & !(v_bool_24_525') & v_int_27_523'=1 & v_node_27_521'
*/

relation r(int n,int x).
relation r2(int n,int x).
int length(node x)
  infer [r,r2]
  requires x::clist<_>@L & Loop
  ensures r(n,res);
  /* requires x::ls<n,null>@L & Term[n] */
  /* ensures r2(res,n); */
{
	if (x == null)
      return 0;
	else 
	  return 1+length(x.next);
}



