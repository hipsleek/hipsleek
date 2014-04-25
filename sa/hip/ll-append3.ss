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

/* HeapPred H(node a). */
//HeapPred H1(node a).
/* HeapPred G2(node a, node b). */
HeapPred G1(node a, node b).
  /* HeapPred G3(node b,node c, node d). */

HeapPred H1(node a).
/* HeapPred H2(node a). */
//HeapPred G1(node a, node b, node c).

/* HeapPred HP1(node a, node b). */
/* HeapPred HP_648(node a). */
/* HeapPred HP_641(node a, node b). */
/* HeapPred T1(node a). */
/* HeapPred T2(node a, node b). */


/* ll<> == self=null */
/*   or self::node<_,q>*q::ll<> */
/*   inv true; */

/*
l2<y> == self::node<a,null> & y=self
  or self::node<_,q>*q::l2<y> 
  inv y!=null;
*/

ll<> == self=null
  or self::node<_,q>*q::ll<>
  inv true;

lseg<p> == self=p
  or self::node<_,q>*q::lseg<p>
  inv true;

void append(node x, node y)

//G1 can not be a lseg because y!=null
/*
  requires x::ll<> * y::ll<> & x!=null
  ensures x::ll<>;

  requires x::ll<> * y::node<a,null> & x!=null
  ensures x::lseg<y>*y::node<a,null>;

*/

  infer[H1,G1]
  requires H1(x)*y::node<a,null>
     ensures G1(x,y) *y::node<a,null>;


{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}
/*
void append2(node x, node y)

//G1 can not be a lseg because y!=null
  infer[H1,G1]
  requires H1(x)*y::node<a,null>
     ensures G1(x,y) *y::node<a,null>;


{
  if (x.next == null)
    x.next = y;
  else
    append2(x.next, y);
}
*/
/*
[ HP_RELDEFN HP_644
HP_644(y_643,y) ::=
 emp&y_643=y
 or y_643::node<val_80_642,y_647> * HP_644(y_647,y) *
    y::node<a,flted_75_602>&flted_75_602=null //WRONG
 ,
 HP_RELDEFN H1
H1(x) ::= x::node<val_80_649,next_80_650> * next_80_650::ll[LHSCase]&true,
 HP_RELDEFN G1
G1(x,y) ::= x::node<val_80_642,y_643> * HP_644(y_643,y)&true]

 */

