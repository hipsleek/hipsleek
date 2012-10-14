
constrs []:{ x::node<_,b> * G1(b,y)&y!=null & b!=null -> G1(x,y),
	HP1(a,x) * x::node<_,y>&a=null -> G1(x,y),
	HP1(b,x)&b!=null -> H1(b),
	H1(x) -> x::node<_,b> * HP1(b,x)
	}

//hp_defs [y]:{ 	H1(x) ->  x::node<_,b>&b=null or x::node<_,b> * H1(b),
//		G1(x,y) -> x::node<_,y> or x::node<_,b> * G1(b,y) & b!= null & y!= null  }

hp_defs [y]:{ HP_648(x) -> x=null or x::node<_,p> * HP_648(p),
        HP_641(p,y) ->p=y or p::node<_,p1> * HP_641(p1,y) & p!=null & y!=null,
        H1(x) ->  x::node<_,p> *  HP_648(p),
		G1(x,y) -> x::node<_,p> *  HP_641(p,y)  }


//y?
