data node{
	int val;
	node next;
}

ll<> == self = null  or self::node<_, q> * q::ll<>;


HeapPred H(node a).
HeapPred G1(node a).
HeapPred G(node a, node r).

node foo(node x)
/*
  requires x::ll<> & x!=null 
   ensures x::ll<> & x!=null & res=x;
*/ 
  infer [H,G]
  requires H(x)
     ensures G(x,res);

{
  if (x.next != null)
    x.next = foo(x.next);
  //  dprint;
 return x;
}

/*


[ H(x)&true --> x::node<val_22_792,next_22_793>@M 
        * (HP_794(next_22_793))&true,

 HP_794(next_22_793)&next_22_793!=null --> H(next_22_793)&true,

 (G(next_22_793,r_812)) * x::node<val_22_792,next_22_793>@M&
  next_22_793!=null --> G(x,r_814)&true,

 (HP_794(next_22_793)) * x::node<val_22_792,next_22_793>@M&
  next_22_793=null --> G(x,r_815)&true]


 H(x_849) ::= x_849::node<val_22_792,next_22_793>@M * next_22_793::ll@M[LHSCase]&true,
 G(x_851,r_852) ::= x_851::node<val_22_792,next_22_793>@M * (HP_853(next_22_793,r_852))&true,
       MISSING x=r? can capture?
 HP_853(next_22_793,r_856) ::= 
 emp&next_22_793=null
 or next_22_793::node<val_22_792,next_22_854>@M * 
    (HP_853(next_22_854,r_812))&true
 ]

*/
