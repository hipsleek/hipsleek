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

bool rand() 
 requires true
 ensures res or !res;

int count(node2 z)
  /*  requires z::bst0<> */
  /* ensures  z::bst0<>; */
  infer[H1,G1]
  requires H1(z)
  ensures G1(z);
{
	node2 cleft;

	if (z == null)
		return 0;
	else
	{
                if (rand()) {
                  cleft = z.left;
                  }
                else {
                  cleft = z.right;
                  };
		return (1 + count(cleft));
	}
}

/*
UNIFICATION of dangling important here!

(i) Can I first identify G1(z) ::= H1(z)

(ii) --sa-unify-dangling
     Identify dangling predicates:
        HP_548, HP_552
     Unify with branches
     HP_552 = H1 = HP_548


[ H1(z_589) ::= 
 z_589::node2<val_32_517',left_32_518',right_32_519'>@M * 
 HP_548(right_32_519') * H1(left_32_518')&true
 or z_589::node2<val_35_587,left_35_588,right_35_522'>@M * 
    HP_552(left_35_588) * H1(right_35_522')&true
 or emp&z_589=null
 ,
 G1(z_590) ::= 
 HP_548(right_32_562) * z_590::node2<val_32_561,cleft_578,right_32_562>@M * 
 G1(cleft_578)&true
 or HP_552(left_35_566) * z_590::node2<val_35_565,left_35_566,cleft_582>@M * 
    G1(cleft_582)&true
 or emp&z_590=null
 ]

--sa-unify-dangling now produce below..

[ H1(z_589) ::= 
 z_589::node2<val_32_517',left_32_518',right_32_519'>@M * 
 H1(right_32_519') * H1(left_32_518')&true
 or z_589::node2<val_35_587,left_35_588,right_35_522'>@M * H1(left_35_588) * 
    H1(right_35_522')&true
 or emp&z_589=null
 ,
 G1(z_590) ::= H1(z_590)&true]

*/

