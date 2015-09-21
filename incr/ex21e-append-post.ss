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

	
HeapPred P(node x, node y).

void append(node x, node y)
  infer [P,@classic]
  requires x::ll<> & x!=null
  ensures P(x,y) ;
{    
	if (x.next == null) 
           x.next = y;
	else
           append(x.next, y);
}


/*
# ex21e.ss

  infer [P,@classic]
  requires x::ll<> & x!=null
  ensures P(x,y) ;

--old-pred-synthesis

[ P(x_1660,y_1661) ::= x_1660::node<Anon_1662,y_1661>@M
 or x_1660::node<Anon_1662,q_1631>@M * P(q_1631,y_1661)&
    x_1660!=null & q_1631!=null
 (4,5)]

// POST

x::node<Anon_1630,q_1631>@M * GP_1659(q_1631,y,x@NI)&
  x!=null & q_1631!=null --> P(x,y)&true,

// POST
P(q_1631,y)&q_1631!=null & x!=null --> GP_1659(q_1631,y,x@NI)&true,

// POST
x::node<Anon_1630,y>@M&x!=null --> P(x,y)&true]

--------------------
GP_1659(q_1631,y,x@NI) <-- P(q_1631,y)&q_1631!=null & x!=null --> 
// form eqn
GP_1659(q_1631,y,x@NI) == P(q_1631,y)&q_1631!=null & x!=null --> 

P(x,y) <-- x::node<Anon_1630,q_1631>@M * GP_1659(q_1631,y,x@NI)&
  x!=null & q_1631!=null 
// unfold GP_1659
P(x,y) <-- x::node<Anon_1630,q_1631>@M * P(q_1631,y) & q_1631!=null 
// unfold GP_1659

P(x,y) <-- x::node<Anon_1630,y>@M&x!=null 

// merge
P(x,y) <-- x::node<Anon_1630,q_1631>@M * P(q_1631,y) & q_1631!=null 
        \/ x::node<Anon_1630,y>@M

P(x,y) <-- x::node<_,q>@M * U(q,y)

P(x,y) <-- U<_,q>*q::node<_,y>

P(x,y) --> x::lseg<q> & x!=null

*/
