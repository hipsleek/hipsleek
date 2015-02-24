class e1 extends __Exc {}
class e2 extends e1 {}
class e3 extends e2 {}
class e4 extends e2 {}
class e5 extends e4 {}



// NOTE : seems that res rather than eres is recognized.
// also no upcasting from e4<> to e1<>
void m1 (ref int i, e1 z) throws e1
	requires true
	ensures i<=0 & i'=i+2 & flow __norm
         or i>0 & i'=2 & flow e5
        ;//'
{
  try{
	try{
      if (i>0) raise new e1();
      dprint;
      i=i+2;
	}catch (e1 v){
		i=2;
        raise new e5();
	};
  } catch (e3 v) {
    assert false;
  };
}


