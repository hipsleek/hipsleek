data node {
  int val;
  node next;
}


HeapPred H1(node a).
HeapPred H2(node a).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).

HeapPred H(node a, node b).
HeapPred G(node a, node b, node c, node d).


void reverse(ref node x, ref node y)
  infer[H1,H2,G]
  requires H1(x) * H2(y)
  ensures G(x',y');
{
	if(x!= null){
		node tmp = x.next;
		x.next = y;
		y = x;
		x = tmp;
		reverse(x,y);
	}
}

/*
byhand

H1(x) * H2(y) & x!=null
for x.next H1(x) * H2(y) & x!=null --> x::node<_,b>
	state: HP_1(x,b) * H2(y) * x::node<_,b> & x!=null
	constr: H1(x) * H2(y) & x!=null --> x::node<_,b> * HP_1(x,b)
HP_1(x,b) * H2(y) * x::node<_,b> & x!=null &tmp = b
HP_1(x,b) * H2(y) * x::node<_,b> & x!=null &tmp = b *y'=x
HP_1(x,b) * H2(y) * x::node<_,b> & x!=null &tmp = b *y'=x & x' = tmp
func call HP_1(x,b) * H2(y) * x::node<_,b> & x!=null &tmp = b *y'=x & x' = tmp --> H(x',y') --* G(x'',y'')
	state: G(x',y') * HP_1(x,b) * H2(y) * x::node<_,b> & x!=null &tmp = b *y0=x & x0 = tmp 
	constr: HP_1(x,b) * H2(y) * x::node<_,b> & x!=null &tmp = b *y'=x & x' = tmp --> H(x',y')
G(x',y') * HP_1(x,b) * H2(y) * x::node<_,b> & x!=null &tmp = b *y0=x & x0 = tmp --> G(x',y')

constr: 
H(x,y) & x=null ---> G(x,y)
H1(x) * H2(y) & x!=null --> x::node<_,b> * HP_1(x,b) * H2(y) 
HP_1(y',x') * H2(x') * y'::node<_,x'> & y'!=null --> H(x',y')
G(x',y') * HP_1(y0,x0) * H2(y) * y0::node<_,x0> & y0!=null--> G(x',y')


H(x,y) & x=null ---> G(x,y)
H1(x) * H2(y)&x!=null --->  x::node<val_22_532',next_22_533'> * HP_551(next_22_533',y,x)
HP_551(tmp_19',y,x) * x::node<val_22_558,y>&x!=null ---> H1(tmp_19') * H2(x)
x::node<val_22_558,y> * G(x',y') * HP_569(y,x',y',x)&x!=null ---> G(x',y')




*/
