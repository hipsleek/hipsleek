/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

/* append two singly linked lists */
void hd(node x)
  infer [n1]
  requires x::ll<n1>
  ensures true;
{    
  int v;
  v = x.val;
  x = x.next;
}
/*
TODO : post has been unfolded.
NEW SPECS:  EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase] & n1!=0 &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           x::node<Anon_526,q_527>@M[Orig] * 
           q_527::ll<flted_11_525>@M[Orig] & n1=flted_11_525+1 & 0<=n1 &
           {FLOW,(20,21)=__norm}

*/


