//class ret_int extends __Exc{  int val} //exception when return from a loop

int test(int a)
 requires true
  ensures a>1 & res=a | a<=1 & res=2;
{
  try {
    loop(a);
    return 2;
  } catch (ret_int r) {
    return r.val;
  };
}

void loop(int a)
  requires true
  ensures  eres::ret_int<a> & a>1 & flow ret_int or a<=1 & flow __norm;
{
  if (a>1) {
    raise new ret_int(a);
    dprint;
    loop(a);
  }
} 


/*
# test2-orig.ss

What is the cause of warning below?

WARNING: test2-orig.ss_17:52_17:70:the result type __norm is not covered by the throw list[]

*/
