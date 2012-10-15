ass []:{ x::node<_,b> * G1(b,y)&y!=null & b!=null -> G1(x,y),
	HP1(a,x) * x::node<_,y>&a=null -> G1(x,y),
	HP1(b,x)&b!=null -> H1(b),
	H1(x) -> x::node<_,b> * HP1(b,x)
	}


hp_defs [H1,G1,y]:{ T1(x) -> x=null or x::node<_,p> * T1(p),
        T2(p,y) ->p=y or p::node<_,p1> * T2(p1,y) & p!=null & y!=null,
        H1(x) ->  x::node<_,p> *  T1(p),
		G1(x,y) -> x::node<_,p> *  T2(p,y)  }

