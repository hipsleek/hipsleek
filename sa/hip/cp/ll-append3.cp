HeapPred HP_1(node a).
HeapPred HP_2(node a, node b).
HeapPred HP_617(node a).

append[
ass [H1,G1]:{ x::node<_,b> * G1(b,y)&y!=null & b!=null --> G1(x,y);
	HP_617(a) * x::node<_,y>&a=null --> G1(x,y);
	HP_617(b)&b!=null --> H1(b);
	H1(x) --> x::node<_,b> * HP_617(b)
	}

hpdefs [H1,G1]:{H1(x) --> x::node<_,p>*HP_1(p);
   HP_1(x) --> x=null or x::node<_,p1> * HP_1(p1);
   G1(x,y) --> x::node<_,p> * HP_2(p,y);
   HP_2(x,p) --> x=p or x::node<_,p1> * HP_2(p1,p)
 }
]
