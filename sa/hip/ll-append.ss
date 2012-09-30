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
HeapPred G2(node a, node b).
HeapPred G1(node a, node b).
  HeapPred G3(node b,node c, node d).

HeapPred H1(node a).
HeapPred H2(node a).
//HeapPred G1(node a, node b, node c).

ll<> == self=null
  or self::node<_,q>*q::ll<>
  inv true;

lseg<p> == self=p
  or self::node<_,q>*q::lseg<p>
  inv true;

void append(node x, node y)
  infer[H1,G1]
// requires H(x)&y=null
  /* ensures G1(x,y);//' */
  requires H1(x)*y::node<a,null>
  ensures G1(x ,y);//'

  /* requires x::ll<> * y::ll<> & x!=null */
  /* ensures  x::ll<> ;  */
  /* requires x::lseg<null> & x!=null  // H(x,y) */
  /* ensures  x::lseg<y> ;             // G(x,y) */

  /* infer[G1, G2] */
  /* requires G1(x,y) */
  /* ensures G2(x,y); */
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

/*
ll:
(1) HP_561(v_node_74_578,y,x) * x::node<val_74_567,y> &  v_node_74_578=null --> G1(x,y)
(2) H1(x) * H2(y) --> x::node<val_74_542',next_74_543'> * HP_561(next_74_543',y,x)
(3) HP_561(v_node_74_584,y,x) * x::node<val_74_569,v_node_74_584> & v_node_74_584!=null --> H1(v_node_74_584) * H2(y)
(4) x::node<val_74_569,v_node_74_584> * G1(v_node_74_584,y) & v_node_74_584!=null --> G1(x,y)
 */
/*
lseg:
(1) HP_561(v_node_74_578,y,x) * x::node<val_74_567,y> &  v_node_74_578=null --> G1(x,y)
(2) G(x,y)&true --> x::node<val_74_542',next_74_543'> * HP_561(next_74_543',y,x)
(3) HP_561(v_node_74_584,y,x) * x::node<val_74_569,v_node_74_584> & v_node_74_584!=null --> G(v_node_74_584,y)
(4) x::node<val_74_569,v_node_74_584> * G1(v_node_74_584,y) & v_node_74_584!=null --> G1(x,y)
 */

/*
5-sep
by-hand:
H(x,y) -> H1(x,y,b) * x::node<_,b>
H1(x,y,b) * x::node<_,y> & b = null-> G(x,x,y)
H1(x,y,b) * x::node<_,b> & b != null |- H(b,y)
G(b, b', y) * x::node<_,b> & b != null  -> G(x,x,y)
auto:
H1(x) * H2(y)--> x::node<_,b> * HP_549(b,y,x)
HP_549(b,y,x) * x::node<_,y>&  b=null --> G1(x,x,y)
HP_549(b,y,x) * x::node<_,b>& b!=null--> H1(b) * H2(y)
x::node<_,b> *  G1(b,b',y)&b!=null --> G1(x,x,y)

//Matched

H(x,y) -> H1(x,y,b) * x::node<_,b>
H1(x,y,b) * x::node<_,y> & b = null-> G(x,x,y)
H1(x,y,b) * x::node<_,b> & b != null -> H(b,y)
G(b, b', y) * x::node<_,b> & b != null  -> G(x,x,y)

Drop para
H(x,y) -> H1(y,b) * x::node<_,b>
H1(y,b) * x::node<_,y> & b = null-> G(x,x,y)
H1(y,b) * x::node<_,b> & b != null -> H(b,y)
G(b, b', y) * x::node<_,b> & b != null  -> G(x,x,y)

substitute
H(x,y) -> H1(y,b) * x::node<_,b>
H1(y,b) * x::node<_,b> & b != null -> H(b,y)
==> H1(y,b) * x::node<_,b> & b != null -> H1(y,b') * b::node<_,b'>

Find def


==> H1(y,b) & b != null -> H1(y,b') * b::node<_,b'>
==> H1(y,b) -> b != null -> H1(y,b') * b::node<_,b'>
new assume: H1(y,b') * b::node<_,b'> & b != null -> H(b,y)


*/
