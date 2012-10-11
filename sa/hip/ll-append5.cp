constrs [H1,H2]:{  	HP1(a,x) * x::node<_,y>&a=null -> G2(x,y),
		H2(x,y) -> x::node<_,b> * HP1(b,x),
		HP1(a,x)&a!=null -> H2(a,y),
		x::node<_,b> * G2(b,y)&b!=null -> G2(x,y)	}

hp_defs [H2,G2]:{ 	G2(x,y) -> x::node<_,y> or x::node<_,a> * G2(a,y)&a!=null,
		H2(x,y) -> x::node<_,b>&b=null  or x::node<_,b> * H2(b,y)
 }

