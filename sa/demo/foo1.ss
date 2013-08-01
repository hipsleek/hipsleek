data node{
	int val;
	node next;
}

ll<> == self = null  or self::node<_, q> * q::ll<>;


HeapPred H(node a).
HeapPred G(node a).

node foo(node x)
/*
  requires x::ll<> & x!=null 
   ensures x::ll<> & x!=null & res=x;
*/ 
  infer [H,G]
  requires H(x)
  ensures G(x);

{
  if (x.next != null)
    x.next = foo(x.next);
  dprint;
 return x;
}

/*
GENERATED:

[ H(x)&true --> x::node<val_22_788,next_22_789>@M * (HP_790(next_22_789))&true,
 HP_790(next_22_789)&next_22_789!=null --> H(next_22_789)&true,
 (G(next_22_789)) * x::node<val_22_788,next_22_789>@M&
  next_22_789!=null --> G(x)&true,
 (HP_790(next_22_789)) * x::node<val_22_788,next_22_789>@M&
  next_22_789=null --> G(x)&true]
*
====>

[ H(x_836) ::= x_836::node<val_22_788,next_22_789>@M * next_22_789::ll@M[LHSCase]&true,
 G(x_838) ::= x_838::node<val_22_788,next_22_789>@M * next_22_789::ll@M[LHSCase]&true]


*/