class Exp extends __Exc {
  int val;
}

int loop(int x)
//infer [@post_n]
  requires true
  ensures  res=x+1111 & flow __norm;
//ensures eres::Exp<2> & x>0 & flow Exp or x<=0 & res=x+1 & flow __norm;
//ensures res=10;
{
  if (x>0) {
    raise new Exp(888);
    loop(x);
    /* return 2; */
  } else {
    return x+1111;
  }
  dprint;
}

/*
# exc4.ss

This is rightly a failure due to the use of __norm in post-condition

ERROR: at _0:0_0:0 
Message: Post condition cannot be derived.
 


*/
