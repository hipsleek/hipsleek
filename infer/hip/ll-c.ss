/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

/* TODO Inferred spec seems verbose */
void appif(node x, node y)
  infer [n1]
//  requires x::ll<n1> * y::ll<n2>
  requires x::ll<n1> 
  case {
    n1=1 -> ensures true;
    n1!=1 -> ensures true;
  }
{    
	if (x.next == null)
      {
        //assume false;
           x.next = y;
      };
}
/*

TODO : flist denotes a disjunction..

Initial Residual Post : [ q_530::ll<flted_14_528>@M[Orig] * x::node<Anon_529,y>@M[Orig] &
flted_14_528+1=n1 & q_530=null & v_bool_25_504' & q_530=null & 
v_bool_25_504' & {FLOW,(20,21)=__norm}, x::node<Anon_529,q_530>@M[Orig] * q_530::ll<flted_14_528>@M[Orig] &
flted_14_528+1=n1 & q_530!=null & 133::!(v_bool_25_504') & q_530!=null & 
!(v_bool_25_504') & {FLOW,(20,21)=__norm}]
Final Residual Post :  false & false & {FLOW,(20,21)=__norm}
*/

