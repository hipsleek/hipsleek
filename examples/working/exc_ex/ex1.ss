class e1 extends __Exc {}
class e2 extends e1 {}
class e3 extends e2 {}



// NOTE : seems that res rather than eres is recognized.
// also no upcasting from e4<> to e1<>
void m1 (ref int i) throws e1
	requires true
	ensures i>0 & i'=i & flow e1
      or 1<=i' & i'<=2 & flow __norm
        ;//'
{

  if (i>5) {
     raise new e1();
     // why? {FLOW,(36,37)=__Exc}
  }
  try{
	try{
		if (i>0) 
          { 
            raise new e1(); 
          }
        i=1;
	}catch (e2 v){
		i=2;
	};
  } catch (e2 v) {
    assert false;
  };
}


