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
 H1(x)&true --> x::node<val_41_521',next_41_522'> * HP_538(next_41_522')&true,
 HP_538(t_21')&t_21'!=null --> H1(t_21')&true,
 H3(z)&true --> H2(z)&true,
 H2(y)&true --> H3(y)&true,
 HP_538(next_43_550)&next_43_550=null --> emp&true,
 x'::node<val_41_543,y>&H2_y_564=y --> G1(x')&true,
 H2(y)&H2_y_564=y --> G2(y)&true,
 H3(z)&true --> G3(z)&true,
 G1(t_566) * x'::node<val_41_545,t_566>&true --> G1(x')&true,
 G3(y)&true --> G2(y)&true,
 G2(z)&true --> G3(z)&true]

 H2(y)&H2_y_564=y --> G2(y)&true,
 G3(y)&true --> G2(y)&true
 G2(z)&true --> G3(z)&true]
 H3(z)&true --> H2(z)&true
 H2(y)&true --> H3(y)&true
 
 should derive:
 H2(x)  -> G2(x)
 G2(x) <-> G3(x)
 H2(x) <-> H3(x)

instead of:
 HP_538(next_43_550)&next_43_550=null --> emp&true,
 x'::node<val_41_543,y>&H2_y_564=y --> G1(x')&true,

we should have:
 HP_538(next_43_550)&next_43_550=null --> emp&true,
 x'::node<val_41_543,y> & PURE(H2(y)) --> G1(x')&true,

 G1(x_585) ::= x_585::node<val_41_543,y> * HP_586(y)&true,
 H1(x_591) ::= x_591::node<val_41_521',next_41_522'> * next_41_522'::ls[LHSCase]&true,
 H3(z) ::= emp&H2_y_564=z,
 H2(y) ::= emp&H2_y_564=y,
 G3(y) ::= emp&H2_y_564=y,
 G2(z) ::= emp&H2_y_564=z,
 HP_586(y) ::= 
 emp&H2_y_564=y
 or y::node<val_41_543,y_589> * HP_586(y_589)&true

 G1(x_585) ::= x_585::node<val_41_543,y> * HP_586(y)&true,
 H1(x_591) ::= x_591::node<val_41_521',next_41_522'> * next_41_522'::ls[LHSCase]&true,
 HP_586(y) ::= 
 emp & PURE(H2(y))
 or y::node<val_41_543,y_589> * HP_586(y_589)&true

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


