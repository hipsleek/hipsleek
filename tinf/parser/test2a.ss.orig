/*class ret_int extends __Exc{
  int val
} //exception when return from a loop
*/



bool test_bool(bool b)
  requires true
  ensures !b & !res | b & res;
{
  while (!b) 
    requires true
    ensures  eres::ret_bool<b> & !b & flow ret_bool or b & flow __norm;
  {
    return b;
  }
  return true;
}

int test_int(int a)
{
  while (a>1) 
    requires true
    ensures  eres::ret_int<a> & a>1 & flow ret_int or a<=1 & flow __norm;
  {
    return a;
  }
  /*
  while(a<1){
    a = a+1;
  }
  */
  return 1;
}

/*
int  test_int_2(int a,int b)
requires true
 ensures a>1 & b<=1 & res=a | a<=1 & res=2 | a>1 & b>1 & res=3;
{
  while (a>1) 
    requires true
      ensures  eres::ret_int<a> & a>1 & b<=1 & flow ret_int or eres::ret_int<3> & a>1 & b>1 & flow ret_int or a<=1 & flow __norm;
  {
    while(b>1)
      requires true
      ensures  eres::ret_int<3> & b>1 & flow ret_int or b<=1 & flow __norm;
    {
      b = b+1;
      return 3;
    }
    return a;
  }
  return 2;
  dprint;
}
*/
