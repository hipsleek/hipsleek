class e1 extends __Exc {}
class e2 extends e1 {}
class e3 extends e2 {}
class e4 extends e2 {}


// NOTE : seems that res rather than eres is recognized.
// also no upcasting from e4<> to e1<>
void m1 (ref int i, e1 z) throws e1
	case {
		i>0 -> ensures i'=i+1 & flow e2 or i'=2 & flow __norm; // disj is needed as we do not currently track exact flow
		i<=0 -> ensures i'=1 & flow __norm; }

{
	try{
		if (i>0) 
          { 
            i = i+1;
            raise new e2();
          }
        i=1;
	}catch (e3 v){
		i=2;
	};
   // dprint;
}


