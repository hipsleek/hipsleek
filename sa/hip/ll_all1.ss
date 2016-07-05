/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


HeapPred H(node a).
HeapPred H1(node a).
HeapPred H2(node a, node b).
  HeapPred H3(node a, node b, node c).
/* append two singly linked lists */
HeapPred G(node a, node b).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node a, node b, node c).


void append2(node x, node y)
  infer [H2,G2]
  requires H2(x,y)
  ensures G2(x,y);
  /*
HP_599(y_598,y) ::= 
 emp&y_598=y
 or y_598::node<val_42_572,y_602> * HP_599(y_602,y)&true
 ,
H2(x,y) ::= x::node<val_42_547',next_42_548'> * HP_604(next_42_548',y) * HP_597(y)&true,
 HP_RELDEFN G2
G2(x,y) ::= x::node<val_42_572,y_598> * HP_599(y_598,y) * HP_596(y)&true]

Possible answer:
 First obtain:
  H2(x,y) == x::node<_,nil> * P1(y)
    or x::node<_,q> * H2(q,y)
  G2(x,y) == x::node<_,y> * P1(y)
    or x::node<_,q> * G2(x,y)

 Then derive:
  H2(x,y) == x::node<_,q> * P2(q,y)
  P2(x,y) == P1(y) & x=nil
    or x::node<_,q> * H2(q,y)
  G2(x,y) == x::node<_,q> * P3(q,y)
  P3(x,y) == P1(y) & x=y
    or x::node<_,q> * P3(q,y)

        H2(x,y) == x::node<_,q> * P2(q,y)
        P2(x,y) == P1(y) & x=nil
          or x::node<_,q> * H2(q,y)
        G2(x,y) == x::node<_,q> * P3(q,y)
        P3(x,y) == P1(y) & x=y
          or x::node<_,q> * P3(q,y)

   H2(x,y) == x::node<_,q> * P2(q,y) & P1(y)
   P2(x,y) == x=nil
     or x::node<_,q> * P2(q,y)
   G2(x,y) == x::node<_,q> * P3(q,y) * P1(y)
   P3(x,y) == x=y
      or x::node<_,q> * P3(q,y)
  */
{    
	if (x.next == null) 
           x.next = y;
	else
           append2(x.next, y);
}

/*
void append(ref node x, node y)
  infer [H2,G3]
  requires H2(x,y)
  ensures G3(x,x',y); //'
{
	if (x == null)
	      x = y;
	else 
		append(x.next, y);
}
*/


