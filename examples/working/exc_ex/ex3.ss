class e1 extends __Exc {}
class e2 extends e1 {}
class e3 extends e2 {}
class e4 extends e2 {}


// NOTE : seems that res rather than eres is recognized.
// also no upcasting from e4<> to e1<>
void m1 (ref int i, e1 z) throws e1
	requires true
	ensures 
      i>0 & i'=i+1 & flow e3
      or i<=0 & i'=1 & flow __norm
        ;//'
{
	try{
		if (i>0) 
          { 
            i = i+1;
            raise new e3();
          }
        i=1;
	}catch (e4 v){
		i=2;
	};
}


