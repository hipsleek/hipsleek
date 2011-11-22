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
	ensures 
        i>0 & i'=1 & flow e1 
        //or  i>0 & i'=i+2 & flow __norm
        or  i<=0 & i'=i+1 & flow __norm
        ;//'
{   
    if (i>0) 
          { //assume false;
            try {
              i=1;
              raise z; //new e1();
            } catch (e3 v)
            {
              i=2;
              assert true;
              //dprint;
             };
    }
	i=i+1;
    dprint;
}


