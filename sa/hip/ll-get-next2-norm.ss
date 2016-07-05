data node {
  int val;
  node next;
}


HeapPred H1(node a).
HeapPred H2(node a).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).

HeapPred H(node a, node b).
HeapPred G(node a, node b, node c, node d).


void reverse(ref node x)
  infer[H,G]
  requires H(x)
  ensures G(x');
{
	if(x != null){
		x = x.next;
	}
}

/*
H(x) & x!=null --> x::node<val_22_530',next_22_531'> * HP_547(next_22_531',x)
HP_547(x',x) * x::node<val_22_551,x'> & x!=null --> G(x')
H(x) & x=null --> G(x)



*/
