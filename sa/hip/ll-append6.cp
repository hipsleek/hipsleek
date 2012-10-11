constrs [H1,G2]:{y::node<a,b> * HP1(t,x) * x::node<_,y>&t=null & b=null -> G2(x,y),
		H1(x) -> x::node<_,b> * HP1(b,x),
		HP1(a,x)&a!=null -> H1(a) ,
		x::node<_,b> * G2(b,y)&y!=null & b!=null -> G2(x,y) }

hp_defs [H1,G2]:{ 	H1(x) -> x::node<_,b>&b=null  or x::node<_,b> * H1(b),
		G2(x,y) ->  y::node<a,b> * x::node<_,y>&b=null or x::node<_,b> * G2(b,y)&b!=null & y!=null	
 }


