constrs []:{ 	H1a(y) * HP1(a,x) * x::node<_,y>&a=null -> G2(x,y) * H1b(y),
		true -> H1b(y),
		H1(x) -> x::node<_,b> * HP1(b,x),
		HP1(a,x)&a!=null -> H1(a),
		H1a(y) -> H1a(y),
		x::node<_,b> * G2(b,y) * H1b(y)&b!=null -> G2(x,y) * H1b(y),
		true -> H1b(y) }

hp_defs []:{ 
 G2(x,y) -> H1a(y) * x::node<_,y> or x::node<_,b> * G2(b,y)& b!=null,
 H1(x) ->  x::node<_,b>&b=null or x::node<_,b> * H1(b),
 H1a(y) ->  H1b(y),
 H1a(y) -> true,
 H1b(y) ->  true
 }

