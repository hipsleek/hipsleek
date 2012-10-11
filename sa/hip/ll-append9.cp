constrs []:{ 	H1a(y) * HP1(a,x) * x::node<_,y>&a=null -> G2(x,y) * H1a(y),
		emp -> H1a(y),
		H1(x) -> x::node<_,b> * HP1(b,x),
		HP1(a,x)&a!=null -> H1(a),
		H1a(y) -> H1a(y),
		x::node<_,b> * G2(b,y) * H1a(y)&b!=null -> G2(x,y) * H1a(y),
		emp -> H1a(y) }

hp_defs [H1,G2]:{
 H1a(y) ->  true,
 G2(x,y) -> x::node<_,y> or x::node<_,b> * G2(b,y)&b!=null,
 H1(x) -> x::node<_,b>&b=null or x::node<_,b> * H1(b)
 }

