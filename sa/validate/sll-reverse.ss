
data node {
  int val;
  node next;
}

/* ll<n> == self = null & n=0 */
/* 	or self::node<_, q>* q::ll<n-1>  */
/*   inv true; */


ll<> == self = null  
  or self::node<_, q>* q::ll<>;

 HeapPred U(node a).

llu<> == U(self)  
  or self::node<_, q>* q::llu<>;

  lly<> == self::node<_, q>* q::lly<>;

HeapPred H1(node a).
HeapPred H2(node a).
HeapPred G1(node a, node b).


  void reverse(node@R x, node@R y)
      infer [H1,H2,G1]
      requires H1(x) * H2(y)
     ensures G1(x',y');//'

/*
  requires x::ll<> * y::llu<>
  ensures y'::llu<>;//'
*/
{
  if(x!= null){
    node tmp = x.next;
    x.next = y;
    y = x;
    x = tmp;
    //dprint;
    reverse(x,y);
    // dprint;
  }
  // else x=y;
}


/*

 ])


([( H1(x) * H2(y)&x!=null, x::node<val_47_536',next_47_537'> * HP_578(x) * H1(next_47_537')&true),
( HP_577(tmp_21') * HP_578(x) * x::node<val_47_562,y>&x!=null, H1(tmp_21') * HP_579(y) * HP_580(x) * HP_583(x)&true),
( x::node<val_47_562,y> * HP_579(y) * HP_580(x)&x!=null, HP_583(x)&true)],[

HP_577(tmp_21'):: ll
HP_583(x)::  x::node<val_47_562,y> * HP_583(x)&x!=null, 		//node stop at Y :D
HP_584(x)::  x::node<val_47_562,y> * HP_584(x)&x!=null,
H1(x)::  ll
H2(y)::  
 HP_583(y)&true
 or HP_584(y)&true	//what ever at the start :D
 ,
HP_581(x)::  emp&x=null,
HP_582(x)::  emp&x=null,
HP_555(tmp_21',x)::  HP_577(tmp_21') * HP_578(x)&true,	//split
HP_572(y,x)::  HP_579(y) * HP_580(x)&true,
G(x,x,y,y)::  HP_581(x) * HP_582(x) * HP_583(y) * HP_584(y)&true])




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
HX(x) * HY(y) & x!=null -> HX1(b,y,x) * x::node<_,b> * HY(y)
HX1(b,y,x) * HY(y) * x1::node<a,y>  -> HX(b) * HY(x1)
GX(x1, x', x1, y') * HX1(b,y,x) * HY(y) * x1::node<a,y>  -> G(x, x',y, y')
HX(x) * HY(y) & x = null & x' = null -> GX(x, x',y, y')

auto1:
 H1(x) * H2(y)& x!=null --> x::node<_,b> * HP_545(b,y,x)
 HP_545(b,y,x) * x::node<_,y>&x!=null --> H1(b) * H2(x)
 x::node<_,y> * G1(temp,x') * G2(x,y') & x!=null--> G1(x,x') * G2(y,y')
 H1(x) * H2(y)&x=null --> G1(x,x) * G2(y,y)

auto2:
H1(x) * H2(y)&x!=null) --> x::node<val_47_536',next_47_537'> * HP_555(next_47_537',y,x)
HP_555(tmp_21',y,x) * x::node<val_47_562,y>&x!=null) --> H1(tmp_21') * H2(x)
x::node<val_47_562,y> * G(tmp_575,x',x,y')&x!=null --> G(x,x',y,y')
H1(x) * H2(y)&x=null) --> G(x,x,y,y)&true

//In the third relation: auto1: new HP?, auto2: lack infomations?


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
