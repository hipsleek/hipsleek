data node{
	int val;
	node next;
}

//ll<> == self = null  or self::node<_, q> * q::ll<>;
/*
ltwo<p:node> == p::ll<> & self = null  or 
   self::node<_, q> * p::node<_,r> * q::ltwo<r>;
*/

HeapPred HL(node a).
HeapPred H(node a, node b).
HeapPred G(node a, node b).

ltwoB<p:node> == HL(p) & self = null  or 
   self::node<_, q> * p::node<_,r> * q::ltwoB<r>;

bool check_zip_leq (node x, node y)
//infer [H,G]  requires H(x,y)  ensures  G(x,y) & res;
requires x::ltwoB<y>@L  ensures res;
{
   if (x==null) return true;
   else return check_zip_leq(x.next,y.next);
}

/*
# check-zip-leq.ss

--sa-dnc

problem with dnc algo;
pre-predicate derived is too strong

[ H(x_946,y_947) ::= emp&x_946=null,
 G(x_948,y_949) ::= emp&x_948=null
   \/  x_948::node<val_24_930,next_24_931>@M * 
y_949::node<val_24_937,next_24_938>@M * G(next_24_931,next_24_938)]

without --sa-dnc

[ H(x_970,y_971) ::= 
 H(next_24_961,next_24_959) * y_971::node<val_24_958,next_24_959>@M * 
 x_970::node<val_24_960,next_24_961>@M
 or emp&x_970=null
 ,
 G(x_972,y_973) ::= 
 emp&x_972=null
 or x_972::node<val_24_930,next_24_931>@M * 
    y_973::node<val_24_937,next_24_938>@M * G(next_24_931,next_24_938)
 ]

===================================
--en-cp-trace --pred-dis-eup

 How come disjoint H(..) not being combined?
 ALGO: Consider two branches:
    P(..) = (1;0)RHS1
    P(..) = (2;0)RHS2
 We can combine them disjunctively together if
    XPure(RHS1) & XPURE(RHS2) |- false
 This occurs below for both H/G; so they are combined as:
    P(..) = (1;0)RHS1
         \/ (2;0)RHS2

[ H(x_946,y_947) ::=(1;0) emp&x_946=null,
 G(x_948,y_949) ::=(1;0) emp&x_948=null
   \/ (2;0) x_948::node<val_24_930,next_24_931>@M * 
y_949::node<val_24_937,next_24_938>@M * G(next_24_931,next_24_938),
 HP_932(next_24_931,y) * 
  HP_939(next_24_938,x) ::=(2;0) H(next_24_931,next_24_938),
 H(x_959,y_960) ::=(2;0) x_959::node<val_24_930,next_24_931>@M * HP_932(next_24_931,y_960) * 
y_960::node<val_24_937,next_24_958>@M * HP_939(next_24_958,x_959),
 HP_933(y_961,x_962) ::=(2;0) y_961::node<val_24_937,next_24_938>@M * HP_939(next_24_938,x_962)]

--en-cp-trace 

[ H(x_946,y_947) ::=(1;0) emp&x_946=null,
 G(x_948,y_949) ::=(1;0) emp&x_948=null
   \/ (2;0) x_948::node<val_24_930,next_24_931>@M * 
y_949::node<val_24_937,next_24_938>@M * G(next_24_931,next_24_938)]

*/
