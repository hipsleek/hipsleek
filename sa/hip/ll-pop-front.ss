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

(H(x) & x'=x--> x::node<val_164_959',b> * HP_1911(b,x,x)
HP_1911(x',x,x) * x::node<val_164_1920,next_165_963'>&v_node_166_964'=x --> G(x,x')

Normalize
H(x) & x'=x--> x::node<_,b> * HP_1911(b)
HP_1911(x') * x::node<val_164_1920,next_165_963'> --> G(x,x')

by hand

H1(tmp, x) & tmp = x

 H2(tmp, x, b) * x::node<_,b> & tmp = x

H2(tmp, x, b) * x::node<_,b> & tmp = x & x'= b

H3(tmp, x, b, c) * x::node<_,b> * tmp::node<_,null> & tmp = x & x'= b -> G(x,x')

relations:
H(x) -> H1(tmp,x) & tmp = x
H1(tmp,x) -> H2(tmp, x, b) * x::node<_,b>
H2(tmp, x, b) * tmp::node<_,null> -> H3(tmp, x, b, c)
H3(tmp, x, b, c) * x::node<_,b> * tmp::node<_,null> & tmp = x & x'= b -> G(x,x')

normalization
H(x) -> H1(tmp,x) & tmp = x
H1(tmp,x) -> H2(tmp, x, b) * x::node<_,b>
H2(tmp, x, b) --> tmp::node<_,null> * H3(tmp, x, b, c)
H3(tmp, x, b, c) * x::node<_,b> * tmp::node<_,null> & tmp = x & x'= b -> G(x,x')

expect:
H(x) -> H3(b) * x::node<_,b>
H3(b) * x::node<_,b> & x'= b -> G(x,x')

**lost info***
*/

