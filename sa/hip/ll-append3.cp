constrs []:{ x::node<_,b> * G1(b,y)&y!=null & b!=null -> G1(x,y)&true,
	HP1(a,x) * x::node<_,y>&a=null -> G1(x,y)&true,
	HP1(b,x)&b!=null -> H1(b)&true,
	H1(x)&true -> x::node<_,b> * HP1(b,x)&true
	}

hp_defs [y]:{ H1(x) ->  
 x::node<a,b>&b=null or x::node<a,b> * H1(b)&true
,
	G1(x,y) -> x::node<_,y> or x::node<_,b> * G1(b,y) & b!= null & y!= null  }


/*note: a in H1, b in H1: should it equal or not ???  IN OR: need dif add spec var :|*/
