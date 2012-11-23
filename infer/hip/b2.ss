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
  infer [n1,m] 
  // @ post[m]?
  requires x::ll<n1>
  ensures x::ll<m> ; 
  //ensures x::ll<m> & m=n1;
  //ensures x::ll<m> & m>0;
{    
  int v;
  v = x.val;
  x = x.next;
}
/*
TODO : not inferring m since it was existential!
TODO : should convert m to explicit inst
             EXISTS(m: x::ll<m>@M[Orig][LHSCase] & true &
             {FLOW,(20,21)=__norm})
NEW SPECS:  EBase exists (Expl)(Impl)[n1](ex)x::ll<n1>@M[Orig][LHSCase] & n1!=0 &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           x::ll<m_548>@M[Orig][LHSCase] & 0<=n1 & {FLOW,(20,21)=__norm}
*/


