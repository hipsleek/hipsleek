HeapPred HP_1(node a,node b).
HeapPred HP_2(node a, node b).
HeapPred HP_579(node a,node b).
HeapPred HP_611(node a, node b).
HeapPred HP_618(node a,node b).
HeapPred H1a(node a).
HeapPred H1b(node a).

append[
ass [H1,H2]:{  	HP1(a,x) * x::node<_,y>&a=null --> G2(x,y);
		H2(x,y) --> x::node<_,b> * HP1(b,x);
		HP1(a,x)&a!=null --> H2(a,y);
		x::node<_,b> * G2(b,y)&b!=null --> G2(x,y)	}

hpdefs [G2,H2]:{
 H1a(x) --> htrue&true;
 H1b(x) --> htrue&true;
 G2(x,y) --> x::node<_,p> * HP_2(p,y) * H1b(y);
 H2(x,y) --> x::node<_,p>*HP_1(p,y) * H1a(y);
 HP_1(x,y) --> x=null or x::node<_,p1> * HP_1(p1,y);
 HP_2(x,p) --> x=p or x::node<_,p1> * HP_2(p1,p)
 }
]
