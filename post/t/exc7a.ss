class Exp extends __Exc {
  int val;
}

int loop(int x)
 infer [@post_n]
  requires true
  ensures true  & flow __flow;
//ensures eres::Exp<2> & x>0 & flow Exp or x<=0 & res=x+1 & flow __norm;
//ensures res=10;
{
  if (x>0) {
    //dprint;
    if (x>100) raise new Exp(2222);
    else raise new __Exc();
    loop(x);
  } 
  //else {return x+1;}
  // dprint;
  return x+1111;
}

/*
# exc7a.ss

    if (x>100) raise new Exp(2222);
    else raise new __Exc();

Why did we have a failure? Is it due to __Exc()
not containing a value?

Checking procedure loop$int... 
Procedure loop$int FAIL.(2)

Exception Failure("hd") Occurred!
(Program not linked with -g, cannot print stack backtrace)

I think we should just obtain:

  Exp   : res=2222 & x>100 --> post(x,res)
  __Exc :  x<=100 --> post(x,res)

*/
