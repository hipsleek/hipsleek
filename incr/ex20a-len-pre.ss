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

	
HeapPred P(node x).


int length(node x)
  infer [P,@classic,@pure_field]
  requires P(x)
   ensures true;
{    
  if (x==null) return 0;
  else return 1+length(x.next);
}

/*
# ex10a.ss

[ // BIND
(2;0)P(x)&
x!=null --> x::node<val_27_1634,next_27_1635>@M * 
            HP_1636(val_27_1634@NI,x@NI) * HP_1637(next_27_1635,x@NI)&
true,
 // PRE_REC
(2;0)HP_1637(next_27_1635,x@NI)&true |#| x::node<val_27_1634,next_27_1635>@M&
true --> P(next_27_1635)&
true,
 // POST
(2;0)HP_1636(val_27_1634@NI,x@NI)&x'=x --> emp&
true,
 // POST
(1;0)P(x)&x'=x & x'=null --> emp&
true]

-------------------------------
HP_1636(val_27_1634@NI,x@NI) == emp
--------
HP_1637(next_27_1635,x@NI)&true 
    |#| x::node<val_27_1634,next_27_1635>@M& true 
    == P(next_27_1635)&
// drop guard
HP_1637(next_27_1635,x@NI)&true 
    == P(next_27_1635)&
--------
P(x)& x!=null --> x::node<val_27_1634,next_27_1635>@M * 
      HP_1636(val_27_1634@NI,x@NI) * HP_1637(next_27_1635,x@NI)&
// unfold HP_1636
P(x)& x!=null --> x::node<val_27_1634,next_27_1635>@M * 
      HP_1637(next_27_1635,x@NI)&
// unfold HP_1637
P(x)& x!=null --> x::node<val_27_1634,next_27_1635>@M * P(next_27_1635)


P(x) & x=null --> emp&
------------------------------------------------
P(x) --> x!=null --> x::node<val_27_1634,next_27_1635>@M * P(next_27_1635)
      /\  x=null --> emp

P(x) --> x::node<val_27_1634,next_27_1635>@M * P(next_27_1635) & x!=null
      \/  emp & x=null

Make Predicate
==============
P(x) == x::node<val_27_1634,next_27_1635>@M * P(next_27_1635) & x!=null
      \/  emp & x=null


*/
