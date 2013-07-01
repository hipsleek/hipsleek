data node {
	int val; 
	node next;	
}

HeapPred H1(node a).
HeapPred H2(node a).
HeapPred H3(node a).
HeapPred G1(node a).
HeapPred G2(node a).
HeapPred G3(node a).

ls<> == self=null 
  or self::node<_,q>*q::ls<>
 inv true;

void swap(ref node x, node y, node z)
  infer [H1,H2,H3,G1,G2,G3]
  requires H1(x)*H2(y)*H3(z)
  ensures G1(x')*G2(y)*G3(z);//'
  /*

*************************************
*******relational assumption ********
*************************************
[ H1(x)&true --> x::node<val_82_521',next_82_522'>@M * HP_538(next_82_522')&
  true,
 HP_538(t_21')&t_21'!=null --> H1(t_21')&true,
 HP_538(next_84_550)&next_84_550=null --> emp&true,
 x'::node<val_82_543,y>@M& XPURE(H2(y)) --> G1(x')&true,
 G1(t_565) * x'::node<val_82_545,t_565>@M&true --> G1(x')&true,
 H3(z)&true --> H2(z)&true,
 H2(y)&true --> H3(y)&true,
 H2(y)&true --> G2(y)&true,
 H3(z)&true --> G3(z)&true,
 G3(y)&true --> G2(y)&true,
 G2(z)&true --> G3(z)&true]
*************************************
Definition of dangling predicate:
 - a predicate is dangling if it is undefined or it
   has no memory footprint.
 - Though such predicates may contain data stucture,
   they are not being accessed by a given method

A dangling predicate that appears in the precondition is
an input dangling predicate, while that from a postcondition
is referred to an output dangling predicate.

In the case of dangling predicate, we are mostly interested
in how the input predicates are related to one another,
and how the output predicate can be defined in terms of
the input dangling predicate.

From:
 G3(y)&true --> G2(y)&true,
 G2(z)&true --> G3(z)&true]

We infer that input dangling are related as follows;
 G3(y) <-> G2(y)

We also infer that output dangling are related as follows;
 H2(y) <-> H3(y)

Lastly, we may define output in terms of input, as follows:

 H2(y) ::= G2(y)
 H3(y) ::= G3(y)

Thus, while we may expect:
 G2(y) ::= y=DLING_G2
We also expect:
 G3(z) ::= z=DLING_G2
 H3(y) ::= y=DLING_G2
 H4(y) ::= y=DLING_G2

However, if we chose to have two dangling inputs, we would have:
 G2(y) ::= y=DLING_G2
 G3(y) ::= y=DLING_G3

 Pure(G2(y)) ::= G2(y) or G3(y)
 




*************************************
*******relational definition ********
*************************************
[ G1(x_581) ::= x_581::node<val_82_543,y>@M * HP_582(y)&true,
 H1(x_587) ::= x_587::node<val_82_521',next_82_522'>@M * next_82_522'::ls[LHSCase]&true,
 HP_582(y) ::= 
 y::node<val_82_543,y_585>@M * HP_582(y_585)&true
 or emp& XPURE(H2(y))
 H2(y) ::= 
 G2(y)&true
 or H3(y)&true
 or G3(y)&true
 ,
 H3(z) ::= 
 G3(z)&true
 or H2(z)&true
 or G2(z)&true
 ,
 G3(y) ::= 
 G2(y)&true
 or H3(y)&true
 ,
 G2(z) ::= 
 G3(z)&true
 or H2(z)&true
 ]



  */
{
    node t = x.next;
	if (t == null){
	      x.next = y;	
}
	else {
           swap(t, z, y);
              x.next=t;
}
}


