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

lseg<p> == self=p
  or self::node<_, q> * q::lseg<p>
  inv true;


HeapPred P(node x, node y).

node append(node x, node y)
  infer [P,@classic]
  requires P(x,y)
  ensures true;
{    
  if (x==null) return y;
  else {
      x.next = append(x.next, y);
      return x;
  }
}


/*
# ex21p1.ss --old-pred-synthesis
node append(node x, node y)
  infer [P,@classic]
  requires P(x,y)
  ensures true;
*******relational definition********
*********************************************************
[ P(x_1664,y_1665) ::= x_1664::ll<>@M(4,5)]
*************************************



P(x,y)& x!=null --> x::node<val_33_1643,next_33_1644>@M * 
            HP_1645(next_33_1644,y,x@NI).

HP_1645(next_33_1644,y,x@NI)&
  true |#| x::node<val_33_1643,next_33_1644>@M&true --> P(next_33_1644,y).

P(x,y)&y'=y & x'=x & res=y' & x'=null --> emp.

==============

HP_1645(next_33_1644,y,x@NI)& true 
   |#| x::node<val_33_1643,next_33_1644>@M&true 
   --> P(next_33_1644,y).

HP_1645(next_33_1644,y,x@NI)& true 
   |#| x::node<val_33_1643,next_33_1644>@M&true 
   == P(next_33_1644,y).

=================
P(x,y)& x!=null --> x::node<val_33_1643,next_33_1644>@M * 
            HP_1645(next_33_1644,y,x@NI).
// unfold
P(x,y)& x!=null --> x::node<val_33_1643,next_33_1644>@M * 
            P(next_33_1644,y).

P(x,y)&y'=y & x'=x & res=y' & x'=null --> emp.
// tidy LHS
P(x,y)& (exists y',x,res: y'=y & x'=x & res=y' & x'=null) --> emp.
P(x,y)& x=null --> emp.



P(x,y)& x!=null --> x::node<val_33_1643,next_33_1644>@M * 
            P(next_33_1644,y).
P(x,y)& x=null --> emp.
   P --> a & B \/ not(a) & C
 ------------------------------------
  P & a --> B /\ P & not(a) --> C
// merging
P(x,y) --> x=null or
   x::node<val_33_1643,next_33_1644>@M * 
            P(next_33_1644,y) & x!=null.
// make defn
P(x,y) === x=null or
       x::node<val_33_1643,next_33_1644>@M * 
            P(next_33_1644,y) & x!=null.


*/
