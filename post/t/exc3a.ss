class Exp extends __Exc {
  int val;
}

int loop(int x)
 infer [@post_n]
  requires true
  ensures true
   // & flow __flow // critical to use __flow
 ;
//ensures eres::Exp<2> & x>0 & flow Exp or x<=0 & res=x+1 & flow __norm;
//ensures res=10;
{
  if (x>0) {
    raise new Exp(2222);
    loop(x);
  } 
  //else {return x+1;}
  //dprint;
  return x+1111;
}

/*
# exc3a.ss

 infer [@post_n]
  requires true
  ensures true 
  // & flow __flow // critical to use __flow
 
I think flow __flow should be the default for
post-condition, in general; where it is
not specified; particularly for for
post inference. If inference is not to
be undertaken; I think we could assume
__norm to be the default.

*/
