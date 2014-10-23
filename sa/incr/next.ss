data node {
	int val;
	node next
}

HeapPred H(node a).
  HeapPred G(node a, node b).


node get_next(node x)

  infer[@shape]
  requires true  ensures true;

/*
infer[H,G]
  requires H(x)  ensures G(x,res);
*/
{
  return x.next;
}


/*
*************************************
*******shape relational assumptions ********
*************************************
[ // BIND
(0)H(x)&true --> x::node<val_19_1218,next_19_1219> * HP_1220(next_19_1219)&
true(4,5),
 // POST
(0)HP_1220(res) * x::node<val_19_1218,res>&true --> G(x,res)&
true(4,5)]

*************************************
*******relational definition ********
*************************************
[ H(x_1223) ::= x_1223::node<val_19_1218,DP_DP_HP_1220>(4,5),
 G(x_1224,res_1225) ::= x_1224::node<val_19_1218,res_1225>&res_1225=DP_DP_HP_1220(4,5)]
*************************************


 */
