class e1 extends __Exc {}
class e2 extends e1 {}
class e3 extends e2 {}
class e4 extends e2 {}
class e5 extends e4 {}


// NOTE : seems that res rather than eres is recognized.
// also no upcasting from e4<> to e1<>
void m1 (ref int i, e1 z) throws e1
	requires true
	ensures i>0 & i'=2 & flow __norm
      or i<=1 & i'=1 & flow __norm
        ;//'
{
  try{
	try{
		if (i>0) 
          { 
            raise new e2();
            dprint;
          }
        i=1;
        dprint;
	}catch (e1 v){
		i=2;
        dprint;
	};
  } catch (e1 v) {
    assert false;
    raise new e1();
  };
  dprint;
}


