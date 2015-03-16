data node {
  int val;
  node next;
}


HeapPred H(node a).
HeapPred H1(node a).
HeapPred H2(node a,node b).
HeapPred G2(node a, node b).
HeapPred G1(node a).
HeapPred G3(node b,node c, node d).


ll<> == self=null
  or self::node<_,q>*q::ll<>
  inv true;

lseg<p> == self=p
  or self::node<_,q>*q::lseg<p>
  inv true;

l2<y> == self::node<a,null> & y=self
  or self::node<_,q>*q::l2<y> 
  inv y!=null;

void append(node x, node y)


  infer[H1,G2]
  requires H1(x)
  ensures G2(x,y);

/*
PROBLEM : What happen to base case of G1([x,y]) ??

!! HP_578([v_node_135_595])
     emp&v_node_135_595=null
 or v_node_135_595::node<val_135_559',next_135_560'> * HP_578(next_135_560')&
    true
 
!!! >>>>>> generalize_one_hp: <<<<<<
!!! G1([x,y])
!!!  =:  x::node<val_135_586,v_node_135_601> * G1(v_node_135_601,y)&
v_node_135_601!=null

!!! >>>>>> generalize_one_cs_hp: <<<<<<
!!! H1([x])= x::node<val_135_559',next_135_560'> * HP_578(next_135_560')&true
*/

 /*
ERROR : Inferred def below should not have y::node<..>

HP_RELDEFN G1:  G1(x,y)::  
 x::node<val_121_601,y> * y::node<a,flted_79_594>&flted_79_594=null
 or x::node<val_121_603,v_node_121_618> * G1(v_node_121_618,y)&
    v_node_121_618!=null & y!=null

 */

/*
  infer[H1,G1]
  requires H1(x)*y::node<a,null>
  ensures G1(x ,y);

HP_RELDEFN HP_586:  
  HP_586(v_node_94_603) <->
   emp&v_node_94_603=null
 or v_node_94_603::node<_,next_94_565'> * HP_586(next_94_565')&true
 ,
HP_RELDEFN G1:  G1(x,y) <->
 y::node<a,flted_71_585> * x::node<_,y>&flted_71_585=null
 or x::node<_,v_node_94_609> * G1(v_node_94_609,y)&
    v_node_94_609!=null & y!=null

HP_RELDEFN H1:  H1(x) <->  
   x::node<_,next_94_565'> * HP_586(next_94_565')&true])
*/

// infer[H1,H2,G1]
//  requires H1(x)*H2(y)
//  ensures G1(x,y);

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


HP_565(v_node_77_582)::  
 emp&v_node_77_582=null
 or v_node_77_582::node<val_77_546',next_77_547'> * HP_565(next_77_547')&true
 ,
HP_596(x)::  
 x::node<val_77_571,y>&y=null
 or x::node<val_77_573,v_node_77_588> * HP_596(v_node_77_588)&
    v_node_77_588!=null
HP_597(y)::  emp&y=null,
H(x)::  x::node<val_77_546',next_77_547'> * HP_565(next_77_547')&true,
G1(v_node_77_588,y)::  HP_596(v_node_77_588) * HP_597(y)&true

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
