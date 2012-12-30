data node2 {
  int val;
  node2 left;
  node2 right;
}

bst0<> == self = null
	or self::node2<_, p, q> * p::bst0<> * q::bst0<>
	inv true;

HeapPred G1(node2 a).
HeapPred H1(node2 a).

/*
[ H1(z_562) ::= 
 z_562::node2<val_27_560,left_27_518',right_27_561>@M * 
 HP_540(right_27_561) * H1(left_27_518')&true
 or emp&z_562=null
 ,
 G1(z_563) ::= 
 HP_540(right_27_547) * 
 z_563::node2<val_27_546,v_node2_27_555,right_27_547>@M * G1(v_node2_27_555)&
 true
 or emp&z_563=null
 ]

PROBLEM intermediate predicate shown in wo elim-dangling
 HP_539(v_node2_40_564) ::=  H1(v_node2_40_564)&true]

 H1(z_562) ::=  
 z_562::node2<val_40_560,left_40_518',right_40_561>@M * 
 HP_540(right_40_561) * H1(left_40_518')&true
 or emp&z_562=null
 ,
 G1(z_563) ::=  
 HP_540(right_40_547) * 
 z_563::node2<val_40_546,v_node2_40_555,right_40_547>@M * G1(v_node2_40_555)&
 true
 or emp&z_563=null
 ,

*/
int count(node2 z)
  /*  requires z::bst0<> */
  /* ensures  z::bst0<>; */
  infer[H1,G1]
  requires H1(z)
  ensures G1(z);
{
	int cleft;

	if (z == null)
		return 0;
	else
	{
		cleft = count(z.left);
		return (1 + cleft);
	}
}
