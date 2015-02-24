class e1 extends __Exc {}

class e3 extends __Exc {}

class e2 extends e1    {}
class e4 extends e1    {}
class e5 extends e1    {}

data node{int i; node n;}

void m1 (ref int i, e1 z) throws e1
	requires z::e1<>
	//ensures i'=3 or eres::e1<> & i>0;
	ensures //eres::e4<>&i'=2 or 
		res::e1<> & i>0 & flow e1 or
		i<=0 & i'=3;
{
	try{
		if (i>0) raise z; // new e1();
		// dprint;
	}catch (e2 v){
		i=2;
		//dprint;
		//assert false;
		raise new e4();
	};
	i=3;
}

void m2 (ref int i) throws e1
	requires true
	//ensures i'=3 or eres::e1<> & i>0;
	//ensures eres::e4<>&i'=2;
	//ensures i<=0 & i'=3;
	ensures res::e4<> & i'=2 & flow e4 or i<=0 & i'=3 ;
{
	//dprint;
	try{
		if (i>0) raise new e1();
	}catch (e1 v){
		i=2;
		/*raise new node(1,null);*/
		raise new e4();
	};
		/*
			try{
			} catch (e2 v) {
				// dead code
				assert false;
				i=4;
				raise new e5();
			};
		*/
	i=3;
}




void m(ref int i)
requires i>0 
ensures i'=i+3;
{
	i=i+1;
        dprint;
	i=i+2;
	dprint;
}

