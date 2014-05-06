data node {
	int val;
	node next;
}

HeapPred F(node a).
HeapPred G(node a, int r).

int front(node x)
  infer[F,G]
  requires F(x)
  ensures  emp;
  /*
[ 
HP_540(v_int_14_523') ::=UNKNOWN,
HP_539(next_14_538) ::=UNKNOWN,
F(x_545) ::= x_545::node<val_14_521',next_14_522'> * HP_539(next_14_522') * 
HP_540(val_14_521')&true,
G(x_555,v_int_14_556) ::= x_555::node<v_int_14_556,next_14_538> * HP_539(next_14_538) * HP_540(v_int_14_556)&true]
*/
{
  return x.val;
}

