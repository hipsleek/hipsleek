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

	
HeapPred P(node x, node@NI y).
void append(node x, node y)
  infer [P,@classic]
  requires P(x,y)
  ensures true ;
{    
	if (x.next == null) 
           x.next = y;
	else
           append(x.next, y);
}


/*
# ex21b.ss

  infer [P,@classic]
  requires P(x,y@NI)
  ensures true ;

******************************

  P(x,y@NI) & true 
  --> x::node<val_26_1625,next_26_1626>@M * HP_1627(next_26_1626,y@NI,x@NI)&true,

// HP_1627(next_26_1626,y@NI,x@NI) & next_26_1626!=null 
   |#| x::node<val_26_1625,next_26_1626>@M& true 
   --> P(next_26_1626,y@NI)&true,

// HP_1627(next_26_1626,y@NI,x@NI)& y'=y & x'=x & next_26_1626=null 
   & next_27_1636=next_26_1626 |#| x'::node<val_26_1625,y'>@M & true 
   --> emp&

*********************************************************
*******relational definition********
*********************************************************
[ P(x_1656,y_1657) ::= HP_1666(x_1656)(4,5),
 HP_1666(x_1656) ::= x_1656::node<val_26_1658,next_26_1626>@M * HP_1666(next_26_1626)&
            next_26_1626!=null
 or x_1656::node<val_26_1658,next_26_1626>@M&next_26_1626=null
 (4,5)]

============================================================
 P(x,y@NI) & true 
  --> x::node<val_26_1625,next_26_1626>@M * HP_1627(next_26_1626,y@NI,x@NI)&true,

// HP_1627(next_26_1626,y@NI,x@NI) & next_26_1626!=null |#| x::node<_,next_26_1626>@M& true 
   --> P(next_26_1626,y@NI)&true,

// HP_1627(next_26_1626,y@NI,x@NI)& next_26_1626=null |#| x::node<_,y>@M & true 
   --> emp&

// HP_1627(next_26_1626,y@NI,x@NI) |#| x'::node<_,r>@M & true 
   --> next_26_1626=null  \/ P(next_26_1626,y@NI) & next_26_1626!=null


 P(x,y@NI) & true 
  --> x::node<val_26_1625,next_26_1626>@M * 
   (next_26_1626=null &  \/ P(next_26_1626,y@NI) & next_26_1626!=null) 
 P(x,y@NI) & true 
  --> x::node<val_26_1625,next_26_1626>@M & next_26_1626=null 
      \/ x::node<val_26_1625,next_26_1626>@M P(next_26_1626,y@NI) & next_26_1626!=null) 


      P(x,y) == self::node<_,q>*R(q,y)
      R(y) = self=null
        \/   self::node<_,q>*r::R(y)



*/
