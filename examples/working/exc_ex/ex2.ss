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
        or z::e1<> & i<=0 & i'=i & flow __norm
        ;//'
{   
	try{
		if (i>0) 
          { //assume false;
            try {
            raise z; //new e1();
            dprint;
            } catch (e2 v)
            {
              raise v;
            };
            dprint;
          }
	}catch (e2 v){
		i=2;
		raise new e4();
        dprint;
	};
    assume false;
	i=3;
    dprint;
}


