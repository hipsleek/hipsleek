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
  infer[H,G1]
  requires H(x,y)
  ensures G1(x,x');
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
auto:
H(x,y)&x!=null --> x::node<val_22_532',next_22_533'> * HP_551(next_22_533',y,x)
HP_551(tmp_19',y,x) * x::node<val_22_558,y>&x!=null -->  H(tmp_19',x)
x::node<val_22_558,y> * G(tmp_570,x',x,y')&x!=null --> G(x,x',y,y')
H(x,y)&x=null --> G(x,x,y,y)



New ALGORITHM
1. H(x,y) & x!= null -> x::node<_,q> * HT(y,q)
2. H(x,y) & x = null -> G(x,x,y,y)
3. y'::node<_,y> * HT(y,x') & y'!=null -> H(x',y')
4. x::node<_,y> * HT(y,x0) & x != null * G(x0,x',x,y') -> G(x,x',y,y')
(after elim para)

SPLIT (may lost info)
H(x,y) <-> H1(x) * H2(y)
HT(y,q) <-> HT1(y) * HT2(q)

1. H1(x) * H2(y) & x!= null -> x::node<_,q> * HT1(y) * HT2(q)
2. H1(x) * H2(y) & x = null -> G(x,x,y,y)
3. y'::node<_,y> * HT1(y) * HT2(x') & y'!=null -> H1(x') * H2(y')
4. x::node<_,y> * HT1(y) * HT2(x0) & x != null * G(x0,x',x,y') -> G(x,x',y,y')

(2) Checkeq, subst (option)
(3) Pick partial
1 ::: 	H2(y) -> HT1(y)
	H1(x) * x!= null -> x::node<_,q> * HT2(q)
2 ::: 	H1(x) * H2(y) & x = null -> G(x,x,y,y)     -> ps1 = {x = null -> H1(x)}
3 :::	HT2(x')-> H1(x')
	y'::node<_,y> * HT1(y) & y'!=null -> H2(y')
4 ::: 	x::node<_,y> * HT1(y) * HT2(x0) & x != null * G(x0,x',x,y') -> G(x,x',y,y')

(4) General: no
(5) Subst
2'. H2(y) & x = null -> G(x,x,y,y)  
3.2 + 1.1 ::: 	y'::node<_,y> * HT1(y) & y'!=null -> HT1(y')  
	y'::node<_,y> * H2(y) & y'!=null -> H2(y')
-> ps2{x = null -> H1(x); y'::node<_,y> * HT1(y) & y'!=null -> HT1(y'); y'::node<_,y> * H2(y) & y'!=null -> H2(y')}	
3.1 + 1.2 :::	HT2(x) * x!= null -> x::node<_,q> * HT2(q) -> ps3 {x = null -> H1(x); y'::node<_,y> * HT1(y) & y'!=null -> HT1(y');HT2(x) * x!= null -> x::node<_,q> * HT2(q); ; y'::node<_,y> * H2(y) & y'!=null -> H2(y')}
3.1 + 1.2 ::: H1(x) * x!= null -> x::node<_,q> * H1(q)
		=> complete def: H1 <-> x = null \/  x::node<_,q> * H1(q) & x!= null
	cur_ps {y'::node<_,y> * HT1(y) & y'!=null -> HT1(y');HT2(x) * x!= null -> x::node<_,q> * HT2(q);; y'::node<_,y> * H2(y) & y'!=null -> H2(y'); HT2(x')-> H1(x')}

2 ::: 	x=null -> G1(x)
	x=null -> G2(x)
	H2(y) -> G3(y)
	H2(y) -> G4(y)

4 :::	HT2(x0) -> G1(x0)
	x::node<_,y> * HT1(y) * G3(x) & x != null -> G1(x)	
	G2(x') -> G2(x')
	HT1(y) -> G3(y)
	G4(y') -> G4(y')

Apply partial/complete def:
4.2 ::: x::node<_,y> * HT1(y) * HT1(x) & x != null -> G1(x)	
x::node<_,y> * HT1(y) & x != null -> G1(x)	 ((which rule?)))

(6) over
ps1: y'::node<_,y> * HT1(y) & y'!=null -> HT1(y')
HT2(x) * x!= null -> x::node<_,q> * HT2(q)
y'::node<_,y> * H2(y) & y'!=null -> H2(y')
HT2(x')-> H1(x')
x=null -> G1(x)
x=null -> G2(x)
H2(y) -> G3(y)
H2(y) -> G4(y)
HT2(x0) -> G1(x0)
x::node<_,y> * HT1(y) & x != null -> G1(x)  	 (if apply ps1: loop forever)
HT1(y) -> G3(y)

Over appr:
y'::node<_,y> * H2(y) & y'!=null <-> H2(y')
y'::node<_,y> * HT1(y) & y'!=null <-> HT1(y') (identical with H2)
x::node<_,y> * HT1(y) & x != null -> G1(x)
	x::node<_,y> * HT1(y) & x != null -> G1(x)  ==> HT1(y') -> HT1(y')
	x=null -> G1(x)
	==> G1 <-> x = null \/  x::node<_,q> * H2(q) & x!= null
x=null <-> G2(x)
H2(y) <-> G3(y)
H2(y) <-> G4(y)
H1 <-> x = null \/  x::node<_,q> * H1(q) & x!= null

Final:
H1 <-> x = null \/  x::node<_,q> * H1(q) & x!= null
y'::node<_,y> * H2(y) & y'!=null <-> H2(y')
G1(x) <-> x = null \/  x::node<_,q> * H2(q) & x!= null
x=null <-> G2(x)




*/

