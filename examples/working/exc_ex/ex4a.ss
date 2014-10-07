class e1 extends __Exc {}
class e2 extends e1 {}
class e2a extends e2 {}
class e3 extends e2 {}
class e4 extends e2 {}
class e5 extends e1 {}


// NOTE : seems that res rather than eres is recognized.
// also no upcasting from e4<> to e1<>
void m1 (ref int i, e1 z) throws e1
	requires true
	ensures 
      i>0 & i'=i+1 & flow e2
      or i<=0 & i'=i & flow __norm
      or i>0 & i'=3 & flow __norm
// below is needed as we do not currently track dflow
      //or i>0 & i'=2 & flow __norm
        ;//'
{
	try{
		if (i>0) 
          { 
            try {
              i = i+1;
              raise new e2();
            } catch (e3 _) {
              i=3;
            };
          }
	}catch (e3 v){
		i=2;
	};
    dprint;
}


