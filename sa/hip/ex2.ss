data node {
  int val;
  node next;
}

HeapPred H(node a).
HeapPred H1(node a).
HeapPred G(node a, node b).
HeapPred G1(node a, node b).

ll<> == self=null 
	or self::node<_, q> * q::ll<>
	inv true;

void append(node x, node y)
/*
  requires x::ll<> * y::ll<> & x!=null
  ensures x::ll<>;
*/
  infer [H,G,H1]
 requires H(x) * H1(y)
 ensures  G(x,y); 
 /*
 requires G1(x,y)
 ensures  G(x,y); 
 requires G1(y,x)
 ensures  G(x,y); 
  */
 {
   if (x.next == null) {
     x.next = y;
   } else {
     append(x.next,y);
   }
 }


/*
data node {
  int val;
  node next;
}

HeapPred H1(node a).
HeapPred H2(node a).
  HeapPred G1(node a, node b, node c).

void append(ref node x, node y)
  infer[H1,H2,G1]
  requires H1(x)*H2(y)
  ensures G1(x,x',y);//'
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}
*/
             /*
H1(x) --> x::node<val_16_527',next_16_528'> * HP_552(next_16_528')
H1(x) * H2(y) * x::node<val_16_569,y> --> G1(x,x,y)
H1(x) --> x::node<val_15_524',next_15_525'> * HP_543(next_15_525')
H1(x) --> x::node<val_18_529',next_18_530'> * HP_559(next_18_530')
H2(y) --> H1(v_node_18_531') * H2(y)
H1(x) * H2(y) * G1(v_node_18_572,v_node_18_573,y) --> G1(x,x,y)



             */
