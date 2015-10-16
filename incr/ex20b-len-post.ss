/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<> == self = null  
	or self::node<_, q> * q::ll<> 
  inv true;


	
HeapPred P(node x).


int length(node x)
  infer [P,@classic,@pure_field]
  requires x::ll<>
  ensures P(x);
{    
  if (x==null) return 0;
  else return 1+length(x.next);
}

/*
# ex20b.ss

[ // POST
x::node<Anon_1629,q_1630>@M * GP_1642(q_1630,x@NI)&x!=null --> P(x)&true,
 // POST
P(q_1630)&x!=null --> GP_1642(q_1630,x@NI)&true,
 // POST
x::ll<>@M&x=null --> P(x)&true]

------------------------------
GP_1642(q_1630,x@NI)&true == P(q_1630)&x!=null 

------------------------------
x::node<Anon_1629,q_1630>@M * GP_1642(q_1630,x@NI)&x!=null 
     --> P(x)&true,
// unfold GP_1642
x::node<Anon_1629,q_1630>@M *  P(q_1630) & x!=null &x!=null 
     --> P(x)&true,
// simplify
x::node<Anon_1629,q_1630>@M *  P(q_1630) 
     --> P(x)&true,

x::ll<>@M&x=null --> P(x)&true]
// unfold ll<>
x=null --> P(x)&true]
--------------------------------------------------
x::node<Anon_1629,q_1630>@M *  P(q_1630) 
\/ x=null  -> P(x)&true,

*/
