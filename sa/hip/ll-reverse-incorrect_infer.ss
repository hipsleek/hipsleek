data node {
  int val;
  node next;
}

HeapPred H1(node a).
HeapPred H2(node a).
HeapPred G1(node a, node b).
HeapPred G2(node a, node b).

void reverse(ref node x, ref node y)
  infer[H1,H2,G1,G2]
  requires H1(x)*H2(y)
  ensures G1(x,x')*G2(y,y');
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
 H1(x) * H2(y) & x!=null --> x::node<val_17_526',next_17_527'> * HP_545(next_17_527')
 H1(x) * H2(y) & x!=null  --> x::node<val_18_528',next_18_529'> * HP_549(next_18_529')
 H1(x) * H2(y) * x::node<val_18_562,y> & x!=null & y'=x & x'=tmp_19' --> H1(x') * H2(y')
 H1(x) * H2(y) * x::node<val_18_562,y> * G1(tmp_566,x') * G2(x,y') & x!=null --> G1(x,x') * G2(y,y')
 H1(x) * H2(y) & x'=x & y'=y & x'=null --> G1(x,x') * G2(y,y')

--after simplify
 H1(x) & x!=null --> x::node<val_17_526',next_17_527'> * HP_545(next_17_527')
 H1(x) & x!=null --> x::node<val_18_528',next_18_529'> * HP_549(next_18_529') //duplicate
 H1(x) * x::node<val_18_562,y> & x!=null --> H1(tmp_19') * H2(x)
 H1(x) * H2(y) * x::node<val_18_562,y> * G1(tmp_566,x') * G2(x,y') & x!=null --> G1(x,x') * G2(y,y')
 H1(x) * H2(y) & x=null --> G1(x,x) * G2(y,y)

 */

/*
by hand
HX(x) & x!=null -> HX1(x, b) * x::node<_,b>
HX1(x, b) * HY(y) * x0::node<a,y> & y' = x0 & x' = b -> HX(x') * HY(y')
GX(x1, x') * GY(y0, y') * HX1(x, b) * HY(y) * x0::node<a,y> & y0 = x0  -> GX(x, x') * GY(y, y')
HX(x) * HY(y) & x = null & x' = null -> GX(x, x') * GY(y, y')

auto:
 H1(x) * H2(y)& x!=null --> x::node<_,b> * HP_545(b,y,x)
 HP_545(b,y,x) * x::node<_,y>&x!=null --> H1(b) * H2(x)
 x::node<_,y> * G1(temp,x') * G2(x,y') & x!=null--> G1(x,x') * G2(y,y')
 H1(x) * H2(y)&x=null --> G1(x,x) * G2(y,y)

//In the third relation: x::node<_,y> * G1(temp,x') * G2(x,y') & x!=null--> G1(x,x') * G2(y,y')
I think LHS lost information of Y


uto:
 H1(x) * H2(y)& x!=null --> x::node<_,b> * HP_545(b,y,x)
 HP_545(b,y,x) * x::node<_,y>&x!=null --> H1(b) * H2(x)
 x::node<_,y> * G1(temp,x') * G2(x,y') & x!=null--> G1(x,x') * G2(y,y')
 H1(x) * H2(y)&x=null --> G1(x,x) * G2(y,y)

drop:
 H1(x) * H2(y)& x!=null --> x::node<_,b> * HP_545(b,y)
 HP_545(b,y) * x::node<_,y>&x!=null --> H1(b) * H2(x)
 x::node<_,y> * G1(temp,x') * G2(x,y') & x!=null--> G1(x,x') * G2(y,y')
 H1(x) * H2(y)&x=null --> G1(x,x) * G2(y,y)

Split
 H1(x) * x!=null --> x::node<_,b> * HP_545_1(b)
 H2(y)--> HP_545_2(y)
 HP_545(b,y) --> H1(b)
 HP_545(b,y) * x::node<_,y> --> H2(x)
 x::node<_,y> * G1(temp,x') * G2(x,y') & x!=null--> G1(x,x')
 G2(x,y') --> G2(y,y')
 H2(y) --> G2(y,y)
 H1(x) * &x=null --> G1(x,x)
 
Split2
 H1(x) * x!=null --> x::node<_,b> * HP_545_1(b)
 H2(y)--> HP_545(y)
 HP_545_1(b) --> H1(b)
 HP_545(y) * x::node<_,y> --> H2(x)
 x::node<_,y> * G21(x) & x!=null--> G11(x)
 G1(temp,x') --> G12(x')
 true --> G21(y)
 G22(y') --> G22(y')
 H2(y) --> G21(y)
 H2(y) --> G22(y)
 H1(x) &x=null --> G11(x)
 H1(x) &x=null --> G12(x)


Split2
 H1(x) * x!=null --> x::node<_,b> * HP_545_1(b)
 H2(y)--> HP_545(y)
 HP_545_1(b) --> H1(b)
 HP_545(y) * x::node<_,y> --> H2(x)
 x::node<_,y> & x!=null--> G11(x)
 G1(temp,x') --> G12(x')
 true --> G21(y)
 G22(y') --> G22(y')
 H2(y) --> G21(y)
 H2(y) --> G22(y)
 H1(x) &x=null --> G11(x)
 H1(x) &x=null --> G12(x)


Synthsis defs

H1(x) -> x!= null -> x::node<_,b> * H1(b)
 HP_545_1(b) --> H1(b)
H2(y) * x::node<_,y> --> H2(x)
H1(x)-> x = null








*/
