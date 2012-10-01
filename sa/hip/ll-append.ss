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
  infer[H,G1]
	requires H(x)&y=null
	ensures G1(x,y); 
//  requires H(x)*y::node<a,null>
//  ensures G1(x,y);//'

  /* requires x::ll<> * y::ll<> & x!=null */
  /* ensures  x::ll<> ;  */
  /* requires x::lseg<null> & x!=null  // H(x,y) */
  /* ensures  x::lseg<y> ;             // G(x,y) */

  /* infer[G, G1] */
  /* requires G(x,y) */
  /* ensures G1(x,y); */
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}

/*
Result: //MATCH
HP_561(v_node_74_578,y,x) * x::node<val_74_567,y>&v_node_74_578=null --> G1(x,y)
H1(x) * H2(y) --> x::node<val_74_542',next_74_543'> *  HP_561(next_74_543',y,x)
HP_561(v_node_74_584,y,x) * x::node<val_74_569,v_node_74_584>& v_node_74_584!=null--> H1(v_node_74_584) * H2(y)
x::node<val_74_569,v_node_74_584> * G1(v_node_74_584,y)&v_node_74_584!=null --> G1(x,y)

!!! NEW SIMPLIFIED HP ASSUME:

HP_561(v_node_74_578,y)::  HP_594(y) or H2(y)		//GENERALIZE
HP_593(x)::  x::node<val_74_569,v_node_74_584> * HP_593(v_node_74_584)
H2(y)::  HP_594(y)
G1(x,y)::  HP_593(x) * HP_594(y)	//SPLIT

As if HP_561(v_node_74_578,y,x) * x::node<val_74_567,y>&v_node_74_578=null --> G1(x,y) can infer x::node<val_74_567,y> --> HP_593(x)
 HP_593(x)::  x::node<val_74_569,v_node_74_584> * HP_593(v_node_74_584) or x::node<val_74_567,y> OK

NEW:
HP_561(v_node_74_578,y,x) * x::node<val_74_567,y>&v_node_74_578=null --> G1(x,y)
H1(x) * H2(y) --> x::node<val_74_542',next_74_543'> * HP_561(next_74_543',y,x)
HP_561(v_node_74_584,y,x) * x::node<val_74_569,v_node_74_584>&  v_node_74_584!=null --> H1(v_node_74_584) * H2(y)
x::node<val_74_569,v_node_74_584> * G1(v_node_74_584,y)& v_node_74_584!=null) --> G1(x,y)


HP_593(v_node_74_578)::  v_node_74_578=null
HP_594(y)::  HP_596(y) or H2(y)
H2(y)::  HP_594(y) or HP_596(y)
HP_595(x)::  x::node<val_74_569,v_node_74_584> * HP_595(v_node_74_584)
HP_561(v_node_74_584,y)::  HP_593(v_node_74_584) * HP_594(y)
G1(v_node_74_584,y)::  HP_595(v_node_74_584) * HP_596(y)

*/


/*
1. H1(x) * H2(y) 
for x.next H1(x) * H2(y)  -> x::node<_, b>
	state: H3(x,b,y) * x::node<_, b>
	constr: H1(x) * H2(y) --> H3(x,b,y) * x::node<_, b>
2. H3(x,b,y) * x::node<_, b> & b =null
	3. H3(x,b,y) * x::node<_, y> & b =null
	constr: H1(x,b,y) * x::node<_, y> & b =null --> G1(x,y)
4. H3(x,b,y) * x::node<_, b> & b != null
	H3(x,b,y) * x::node<_, b> & b != null -> H1(b) * H2(y) -> G1(b,y)
	state: 5. G1(b,y) * x::node<_, b> & b != null
	constr: H3(x,b,y) * x::node<_, b> & b != null --> H1(b) * H2(y)
constr G1(b,y) * x::node<_, b> & b != null --> G1(x,y)

constrs: 	
	H1(x) * H2(y) --> H3(x,b,y) * x::node<_, b>
	H3(x,b,y) * x::node<_, y> & b =null --> G1(x,y)
	H3(x,b,y) * x::node<_, b> & b != null --> H1(b) * H2(y)
	G1(b,y) * x::node<_, b> & b != null --> G1(x,y)

drop: 
	H1(x) * H2(y) --> H3(b,y) * x::node<_, b>
	H3(b,y) * x::node<_, y> & b =null --> G1(x,y)
	H3(b,y) * x::node<_, b> & b != null --> H1(b) * H2(y)
	G1(b,y) * x::node<_, b> & b != null --> G1(x,y)

op1:
b = null -> H1(b,y)
x::node<_, y> -> G1(x,y)			//cond: H1(b,y) & b = null
G1(b,y) * x::node<_, b> --> G1(x,y)		//cond: H1(b,y) & b != null
op2:
Pick first:
H2: def already
H32(y) <--> H2(y)
H32(y) * x::node<_, y> --> G1(x,y) ==> H32(y) * b::node<_, y> --> G1(b,y) 
G1(b,y) * x::node<_, b> & b != null --> G1(x,y) ==> H32(y) * b::node<_, y> * x::node<_, b> & b != null --> G1(x,y)


op3:
	H1(x) * H2(y) --> H3(b,y) * x::node<_, b>
	H3(b,y) * x::node<_, y> & b =null --> G1(x,y)
	H3(b,y) * x::node<_, b> & b != null --> H1(b) * H2(y)
	G1(b,y) * x::node<_, b> & b != null --> G1(x,y)
H2(y) -> H32(y)
H32(y) -> G12(y)
H32(y) -> H2(y)

H2,H32,G12
	H1(x) --> H31(b) * x::node<_, b>
	H31(b) * x::node<_, y> & b =null --> G11(x)
	H31(b) & b != null --> H1(b)
	G11(b) * x::node<_, b> & b != null --> G11(x)

b =null -> H31(b) 
H31(b) & b != null --> H31(b') * b::node<_, b'>
H1(x) --> H31(b) * x::node<_, b>
G11(b) * x::node<_, b> --> G11(x)
x::node<_, y> --> G11(x)

op4
	H1(x) * H2(y) --> H3(b,y) * x::node<_, b>
	H3(b,y) * x::node<_, y> & b =null --> G1(x,y)
	H3(b,y) * x::node<_, b> & b != null --> H1(b) * H2(y)
	G1(b,y) * x::node<_, b> & b != null --> G1(x,y)
SPLIT all:
	H1(x) * H2(y) --> H31(b) * H32(y) * x::node<_, b>
	H31(b) * H32(y) * x::node<_, y> & b =null --> G11(x) * G12(y)
	H31(b) * H32(y) * x::node<_, b> & b != null --> H1(b) * H2(y)
	G11(b) * G12(y) * x::node<_, b> & b != null --> G11(x) * G12(y)
SIMPLIFY
	H1(x) --> H31(b) * x::node<_, b>
	H2(y) --> H32(y)
	H32(y) * x::node<_, y> --> G11(x)
 	b =null  --> H31(b)
	H32(y) --> G12(y)
	H31(b) & b != null --> H1(b) 
	H32(y) --> H2(y)
	G11(b) * x::node<_, b> & b != null --> G11(x) 

*/

/*
Constr through LOOP:
Loop1
HP_593(v_node_74_578) * HP_594(y) * x::node<val_74_567,y>&  v_node_74_578=null --> HP_595(x) * HP_596(y)
H1(x) * H2(y) --> x::node<val_74_542',next_74_543'> *   HP_593(next_74_543') * HP_594(y)
HP_593(v_node_74_584) * HP_594(y) * x::node<val_74_569,v_node_74_584>& v_node_74_584!=null --> H1(v_node_74_584) * H2(y)
x::node<val_74_569,v_node_74_584> * HP_595(v_node_74_584)&  v_node_74_584!=null --> HP_595(x)

loop2
HP_594(y) * x::node<val_74_567,y>&v_node_74_578=null --> HP_595(x) *  HP_596(y)
H1(x) * H2(y) --> x::node<val_74_542',next_74_543'> * HP_593(next_74_543') * HP_596(y)
HP_593(v_node_74_584) * HP_594(y) * x::node<val_74_569,v_node_74_584>&  v_node_74_584!=null --> H1(v_node_74_584) * H2(y)

loop3: no changes
HP_594(y) * x::node<val_74_567,y>&v_node_74_578=null --> HP_595(x) *   HP_596(y)
H1(x) * H2(y) --> x::node<val_74_542',next_74_543'> * HP_593(next_74_543') * HP_596(y)
HP_593(v_node_74_584) * HP_594(y) * x::node<val_74_569,v_node_74_584>& v_node_74_584!=null) --> H1(v_node_74_584) * HP_596(y)

DEFS:
HP_593(v_node_74_578):: v_node_74_578=null
HP_594(y):: HP_596(y) or H2(y)
H2(y)::  HP_594(y) or HP_596(y)
HP_595(x)::  x::node<val_74_569,v_node_74_584> * HP_595(v_node_74_584)
HP_561(v_node_74_584,y)::  HP_593(v_node_74_584) * HP_594(y)
G1(v_node_74_584,y)::  HP_595(v_node_74_584) * HP_596(y)


PROBLEM: x::node<val_74_567,y> --> HP_595(x) : it's not well-defined ==> which is Y?
But if: HP_594(y) * x::node<val_74_567,y>&v_node_74_578=null --> G(x,y)
if x point to y => try to merge again



*/

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
