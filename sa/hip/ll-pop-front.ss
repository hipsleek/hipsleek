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
HeapPred G3(node a, node b, node c).
HeapPred G4(node a, node b, node c, node d).

//pop and return first element

node pop_front(ref node x)
  infer[H,G]
  requires H(x) //& m>=1
  ensures  G(x,x'); //' m>=1 & m=n+1
{
  node tmp = x;
  x = x.next;
  tmp.next=null;
  return tmp;
}


/*
by hand
H(x) 
for x.next
constr: H(x) -> x::node<_,b> * H1(x,b)
state: x::node<_,b> * H1(x,b) & tmp =x
x::node<_,b'> * H1(x,b) & tmp = x & x' = b & b' = null -> G(x,x')
 
constrs
H(x) -> x::node<_,b> * H1(x,b)
x::node<_,b'> * H1(x,x') & b' = null -> G(x,x')
drop: 	H(x) -> x::node<_,b> * H1(b)
	x::node<_,b'> * H1(x') & b' = null -> G(x,x')
H1(x') -> G2(x')
H(x) -> x::node<_,b> * H1(b)
x::node<_,b'> & b' = null -> G1(x)
defs:
x::node<_,b'> & b' = null <-> G1(x)
H1(x') -> G2(x')
H(x) -> x::node<_,b> * H1(b)
H(x) <-> x::node<_,b> * G2(b)  ==> ???

//cp: 
H(x) -> x::node<_,b> * H1(x,b)
x::node<_,b'> * H1(x,x') & b' = null -> G(x,x')

H(x)&x'=x --> x::node<val_164_919',next_164_920'> * HP_996(next_164_920',x,x)  			//match
HP_996(x',x,x) * x::node<val_164_1005,next_165_923'>& v_node_166_924'=x --> G(x,x')		//lack of info !!!

( H(x)&x'=x, x::node<val_23_535',next_23_536'> * HP_552(next_23_536',x)&true),
( HP_552(x',x) * x::node<val_23_561,next_24_539'>&v_node_25_540'=x & 
next_24_539'=null, G(x,x')&true)]


!!! NEW SIMPLIFIED HP ASSUME:[HP_RELDEFN HP_996:  HP_996(x')::  HP_1009(x')&true,
HP_RELDEFN G:  G(x,x')::  HP_1008(x) * HP_1009(x')&true]

HP_552(x')::  HP_565(x')&true,
HP_564(x)::  x::node<val_23_561,next_24_539'>&next_24_539'=null & v_node_25_540'=x,
G(x,x')::  HP_564(x) * HP_565(x')&true


*/

