data node {
	int val; 
	node next;	
}

HeapPred H1(node a).
HeapPred H2(node a).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).

void append(ref node x,ref node y)
  infer[H1,H2,G1,G2]
  requires H1(x)*H2(y)
  ensures G1(x,x')*G2(y,y');
{
//1: dprint;
	if (x.next == null){
//2:		dprint;
	      x.next = y;	
}
	else {
		//dprint;
		append(x.next, y);
dprint;
}
}

/*
Line by line: 
//1: H1(x) * H2(y) & x'=x & y'=y
//2:

[(RELASS [H1,H2,HP_544], H1(x), x::node<val_17_525',next_17_526'> * HP_544(next_17_526')

H1(x) * H2(y) & x'=x & y'=y 

//3:

EXISTS(val_19_528': H1(x) * H2(y) * x'::node<val_19_528',y'> & x'=x & y'=y 


H1(x) * H2(y) * G1(v_node_22_568,v_node_22_532') * G2(y,y') & x'=x



by-hand:
H(x,y) -> H1(x,y,b) * x::node<_,b>
H1(x,y,b) * x::node<_,y> & b = null & x' = x & y' = y -> G(x,x',y,y')
H1(x,y,b) * x::node<_,b> & b != null & y' = y |- H(b,y')
G(b, b', y0, y') * x::node<_,b> & b != null & x' = x & y0 = y -> G(x,x',y,y')

H1(x) --> x::node<val_17_528',next_17_529'>@M[Orig] * 
  HP_553(next_17_529'),
 H1(x) * H2(y) * x::node<val_17_571,y>@M[Orig] --> G1(x,x) * G2(y,y)
 H1(x) --> x::node<val_16_525',next_16_526'>@L[Orig] * 
  HP_544(next_16_526'),
 H1(x) --> x::node<val_19_530',next_19_531'> * 
  HP_560(next_19_531')
 H2(y) --> H1(v_node_19_532') * H2(y)
 H1(x) * H2(y) * G2(y,y')--> G1(x,x) * 
  G2(y,y')


gen:
H1(x) --> x::node<_,b> * HP_553(b)
H1(x) * H2(y) * x::node<_,y> --> G1(x,x) * G2(y,y)
H1(x) --> x::node<_,b> * HP_544(b)
H1(x)--> x::node<_,b> * HP_560(b)
H2(y)--> H1(v_node_19_532') * H2(y)
H1(x) * H2(y) * G2(y,y') --> G1(x,x) * G2(y,y')

*/
