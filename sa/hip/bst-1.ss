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

int count(node2 z)
  /*  requires z::bst0<> */
  /* ensures  z::bst0<>; */
  infer[H1,G1]
  requires H1(z)
  ensures G1(z);
{
	int cleft, cright;

	if (z == null)
		return 0;
	else
	{
		cleft = count(z.left);
		cright = count(z.right);
		return (1 + cleft + cright);
	}
}

/*
H1(z)& z!=null --> z::node2<val_28_537',left_28_538',right_28_539'> *
    HP_557(left_28_538',right_28_539');
HP_557(v_node2_28_540',right_28_573) * z::node2<_,v_node2_28_540',right_28_539'> -    -> H1(v_node2_28_540');
z::node2<_,v_node2_27_573,right_27_566>*G1(v_node2_27_573) & z!=null
     -->  H1(right_27_566);
H1(z)&z=null --> G1(z);
z::node2<_,v_node2_28_580,right_28_573> *
     G1(v_node2_28_580) * G1(right_28_573)&true --> G1(z);

 */
