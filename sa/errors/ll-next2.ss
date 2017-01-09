data node {
	int val;
	node next
}

HeapPred H(node a).
HeapPred H1(node a).
HeapPred H2(node a).
HeapPred G(node a, node b).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).
HeapPred HP_535(node a, node b).
HeapPred G3(node a, node b, node c).
HeapPred G4(node a, node b, node c, node d).
HeapPred HP_535(node a, node b).
HeapPred HP_537(node a, node b).
HeapPred HP_557(node a, node b).

/* return the tail of a singly linked list */
node get_next(ref node x)
  infer[H,G3]
  requires H(x)
  ensures G3(x',x,res);//'
/*

  requires x::node<_,q> * HP(q)
  ensures x::node<_,null> * HP(res) & res=q & x'=x; //'

[ HP_RELDEFN HP_559
HP_559(v_node_50_548') ::=UNKNOWN,
 HP_RELDEFN G3
G3(x,v_571,v_node_50_548') ::= HP_559(v_node_50_548') * x::node<val_48_568,next_49_547'>&
next_49_547'=null & x=v_571,
 HP_RELDEFN H
H(x) ::= x::node<val_48_543',next_48_544'> * HP_559(next_48_544')&true]



However, this is missing a relation x'=x or rather
x=v_571. I am also not sure why x' in the original G is being
renamed as x.

[ HP_RELDEFN HP_559
HP_559(v_node_39_548') ::= htrue&true,
 HP_RELDEFN H
H(x) ::= x::node<val_37_543',next_37_544'>&true,
 HP_RELDEFN G3
G3(x,v_571,v_node_39_548') ::= HP_559(v_node_39_548') * 
   x::node<val_37_568,next_38_547'>&next_38_547'=null]

*/
{
  node tmp = x.next;
  x.next = null;
  return tmp;
  //	dprint;
}

/* node get_next_next(ref node x) */
/*   infer[H1,G1] */
/*   requires H1(x) */
/*   ensures G1(x',res);//'n>=1 & n=m+1 */
/* { */
/*   node tmp = x.next.next; */
/*   x.next = null; */
/*   return tmp; */
/*   //	dprint; */
/* } */

/*

H(x) = x::node<_,q>
G(x,res) = x::node<_,null> & res=q

*/

/*

-----constrs------
H(x) --> x::node<val_22_535',next_22_536'> * HP_551(next_22_536',x)
HP_551(v_node_24_540',x) * x::node<val_22_560,next_23_539'> --> G(x,v_node_24_540')

//dprint: HP_551(v_node_24_540',x) * x::node<val_22_560,next_23_539'> & next_23_539'=null
//Lost infomation: next_23_539'=null


------defs---------
H(x)::  x::node<val_22_535',next_22_536'> * HP_566(x) or x::node<val_22_535',next_22_536'> * HP_563(x)
HP_565(v_node_24_540')::  HP_564(v_node_24_540')
HP_566(x)::  HP_563(x)
G(x,v_node_24_540')::  HP_563(x) * HP_564(v_node_24_540')
HP_551(v_node_24_540',x)::  HP_565(v_node_24_540') * HP_566(x)


------new-----constr---------
H(x) --> x::node<val_24_543',next_24_544'> * HP_559(next_24_544')
HP_559(tmp_19') * x::node<val_24_568,next_25_547'>&v_node_26_548'=tmp_19' & next_25_547'=null ---> HP_580(x) * HP_581(v_node_26_548')


------new ----def
HP_559(tmp_19')::  emp&v_node_26_548'=tmp_19',
HP_580(x)::  x::node<val_24_568,next_25_547'>&next_25_547'=null,
HP_581(v_node_26_548')::  emp&v_node_26_548'=tmp_19',
H(x)::  x::node<val_24_543',next_24_544'> * HP_559(next_24_544')&true,
G(x,v_node_26_548')::  HP_580(x) * HP_581(v_node_26_548')&true])

should be HP_559(tmp_19') :: HP_581(v_node_26_548') &v_node_26_548'=tmp_19'


new (3/10)
===================
 H(x) --> x::node<val_25_543',next_25_544'> * HP_559(next_25_544')
 HP_559(tmp_19') * x::node<val_25_568,null>  -->  G(x,tmp_19' )
//Right
([( H(x)&true, x::node<val_25_543',next_25_544'> * HP_559(next_25_544')&true),
( HP_559(tmp_19') * x::node<val_25_568,next_26_547'>&next_26_547'=null & 
v_node_27_548'=tmp_19', G(x,v_node_27_548')&true)],[])

//HP_559(tmp_19')&  v_node_27_548'=tmp_19' -->  G2(v_node_27_548') 
//x::node<val_25_568,next_26_547'>&next_26_547'=null -->  G1(x)
*/











/*


expect:
H(x) -> x::node<_,b> * H1(x,b)
x::node<_,b> * H1(x,b) & tem = b

x::node<_,b'> * H1(x,b) & tem = b * b' = null
 
x::node<_,b'> * H1(x,b) & tem = b * b' = null -> G(x,b)
normalize:

H(x) -> x::node<_,b> * H1(b)
x::node<_,b'> * H1(b) * b' = null -> G(x,b)

//should have null here

final?
H(x) -> x::node<_,b> 
x::node<_,null> -> G(x,b)

expect2:
H(x) -> x::node<_,b> * H1(x,b)
x::node<_,b> * H1(x,b) & tem = b

x'::node<_,null> * H1(x,b) & tem = b 
 
x'::node<_,null> * H1(x,b) & tem = b  -> G(x,b)
normalize:

H(x) -> x::node<_,b> * H1(x,b)
x'::node<_,null> * H1(x,b) -> G(x,b)


final?
H(x) -> x::node<_,b> 
x::node<_,b> -> G(x,b)


*** H(x) -> x::node<_,b> * H1(x,b) *** constrant on node and node next -> change node next***
*/

