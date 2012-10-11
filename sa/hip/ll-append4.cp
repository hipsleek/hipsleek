constrs []:{  	HP1(a,x) * x::node<_,y>&a=null -> G2(x,y) ,
		H1(x)->  x::node<_,b> * HP1(b,x),
		HP1(a,x)&a!=null -> H1(a),
		x::node<_,b> * G2(b,y)&b!=null -> G2(x,y)}

hp_defs [H1, G2]:{ 	
		G2(x,y) -> x::node<_,y> or x::node<_,a> * G2(a,y)&a!=null, 
		H1(x) -> x::node<_,b>&b=null  or x::node<_,b> * H1(b)
 }


