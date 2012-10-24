HeapPred HP_1(node a).
HeapPred HP_2(node a, node b).

append[
ass []:{ 	H1a(y) * HP1(a,x) * x::node<_,y>&a=null --> G2(x,y);
		H1(x) --> x::node<_,a> * HP1(a,x);
		HP1(a,x)&a!=null --> H1(a);
		H1a(y) --> H1a(y);
		x::node<_,b> * G2(b,y)&b!=null --> G2(x,y) }

hpdefs [G2,H1,H1a]:{
 H1a(y) -->  true;
 G2(x,y) --> x::node<_,p> * HP_2(p,y);
 H1(x) --> x::node<_,p>*HP_1(p);
 HP_1(x) --> x=null or x::node<_,p1> * HP_1(p1);
 HP_2(x,p) --> H1a(p) & x=p or x::node<_,p1> * HP_2(p1,p)
 }
]
