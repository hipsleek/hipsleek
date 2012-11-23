class e1 extends __Exc {}

class e3 extends __Exc {}

class e2 extends e1    {}
class e4 extends e1    {}
class e5 extends e1    {}

data node{int i; node n;}

// NOTE : seems that res rather than eres is recognized.
// also no upcasting from e4<> to e1<>
void m1 (ref int i, e1 z) throws e1
	requires z::e1<>
	//ensures i'=3 or eres::e1<> & i>0;
	ensures 
        eres::e4<> & i>0 & i'=2 & flow e4 
        or eres::e1<> & i>0 & i'=i & flow e1
        or z::e1<> & i<=0 & i'=3 & flow __norm
        ;//'
{
	try{
		if (i>0) 
          { //assume false;
            raise z; //new e1();
          }
	}catch (e2 v){
		i=2;
		//dprint;
		raise new e4();
       // dprint;
	};
    //dprint;
	i=3;
}

void m2 (ref int i) throws e1
	requires true
	//ensures i'=3 or eres::e1<> & i>0;
	//ensures eres::e4<>&i'=2;
	//ensures i<=0 & i'=3;
	ensures eres::e4<> & i'=2 & flow e4 or i<=0 & i'=3 ;
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
    //dprint;
	i=i+2;
	//dprint;
}

