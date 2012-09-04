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

