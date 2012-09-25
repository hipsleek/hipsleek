data node {
  int val;
  node next;
}

/* HeapPred H(node a). */
/* HeapPred H1(node a). */
/* HeapPred G(node a, node b). */
/* HeapPred G1(node a, node b). */

/* ll<> == self=null  */
/* 	or self::node<_, q> * q::ll<> */
/* 	inv true; */

/* void append(node x, node y) */
/* /\* */
/*   requires x::ll<> * y::ll<> & x!=null */
/*   ensures x::ll<>; */
/* *\/ */
/*   infer [H,G,H1] */
/*  requires H(x) * H1(y) */
/*  ensures  G(x,y);  */
/*  /\* */
/*  requires G1(x,y) */
/*  ensures  G(x,y);  */
/*  requires G1(y,x) */
/*  ensures  G(x,y);  */
/*   *\/ */
/*  { */
/*    if (x.next == null) { */
/*      x.next = y; */
/*    } else { */
/*      append(x.next,y); */
/*    } */
/*  } */
/*
HP_550(v_node_30_567,y,x) * x::node<val_30_556,y> & v_node_30_567=null --> G(x,y)
H(x) * H1(y) --> x::node<val_30_531',next_30_532'> * HP_550(next_30_532',y,x)
HP_550(v_node_30_573,y,x) * x::node<val_30_558,v_node_30_573> & v_node_30_573!=null --> H(v_node_30_573) * H1(y)
x::node<val_30_558,v_node_30_573> * G(v_node_30_573,y)& v_node_30_573!=null --> G(x,y)
*/


HeapPred H(node a).
HeapPred H1(node a).
HeapPred G(node a, node b).
HeapPred G1(node a, node b).


HeapPred H1(node a).
HeapPred H2(node a).
HeapPred G1(node a, node b).

void append(ref node x, node y)
  infer[H1,H2,G1]
  requires H1(x)*H2(y)
  ensures G1(x',y');//'
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

          /*
H1(x) --> x::node<val_25_530',next_25_531'> * HP_549(next_25_531',x)
HP_549(v_node_25_566,x) * x::node<val_25_555,y> & v_node_25_566=null --> G1(x,x,y)
HP_549(v_node_25_572,x) * x::node<val_25_557,v_node_25_572> & v_node_25_572!=null --> H1(v_node_25_572) * H2(y)
x::node<val_25_557,v_node_25_572> * G1(v_node_25_572,v_node_28_583,y) & v_node_25_572!=null --> G1(x,x,y)

H1(x) * H2(y) --> x::node<val_59_530',next_59_531'> * HP_549(next_59_531',y,x)
HP_549(v_node_59_566,y,x) * x::node<val_59_555,y> & v_node_59_566=null --> G1(x,x,y)
HP_549(v_node_59_572,y,x) * x::node<val_59_557,v_node_59_572>& v_node_59_572!=null --> H1(v_node_59_572) * H2(y)
x::node<val_59_557,v_node_59_572> * G1(v_node_59_572,v_node_62_583,y) & v_node_59_572!=null --> G1(x,x,y)

             */

/*
5-sep
by-hand:
H(x,y) -> H1(x,y,b) * x::node<_,b>
H1(x,y,b) * x::node<_,y> & b = null & x' = x & y' = y -> G(x,x',y,y')
H1(x,y,b) * x::node<_,b> & b != null & y' = y |- H(b,y')
G(b, b', y0, y') * x::node<_,b> & b != null & x' = x & y0 = y -> G(x,x',y,y')
auto:
H1(x) * H2(y)--> x::node<_,b> * HP_549(b,y,x)
HP_549(b,y,x) * x::node<_,y>&  b=null --> G1(x,x,y)
HP_549(b,y,x) * x::node<_,b>& b!=null--> H1(b) * H2(y)
x::node<_,b> *  G1(b,b',y)&b!=null --> G1(x,x,y)

//Matched
*/
