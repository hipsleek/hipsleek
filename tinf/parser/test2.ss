class ret_int extends __Exc{
  int val
} //exception when return from a loop


int test(int a)
 requires true
  ensures a>1 & res=a | a<=1 & res=2;
{
  try {
    loop(a);
  } catch (ret_int r) {
    return r.val;
  };
  return 2;
}

void loop(int a)
  requires true
  ensures  eres::ret_int<a> & a>1 & flow ret_int or a<=1 & flow __norm;
{
  if (a>1) {
    raise new ret_int(a);
    loop(a);
  }
} 
