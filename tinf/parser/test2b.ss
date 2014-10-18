/*class ret_int extends __Exc{
  int val
} //exception when return from a loop
*/


int  test_int(int a,int y)
requires true
 ensures y<=0 & res=0 | y>0 & a>1 & res=a | y>0 & a<=1 & res=2;
{
  while (y>0)
    requires true
    ensures y<=0 & flow __norm
           or eres::ret_int<a> & y>0 & a>1 & flow __RET 
           or eres::ret_int<2> & y>0 & a<=1 & flow __RET;
  {
      while (a>1) 
        requires true
        ensures  eres::ret_int<a> & a>1 & flow __RET or a<=1 & flow __norm;
      {
        return a;
      }
      return 2;
      y--;
   }
   return 0;
  //dprint;
}

/*
# test2b.ss

Starting z3... 
exists_return: unexpected
!exists return
exists_return: unexpected
!!!exists return

Last Proving Location: 1 File "test2b.ss",Line:11,Col:2

ERROR: at test2b.ss_13:18_13:23 
Message: UNIFICATION ERROR : at location {(13,18),(13,23)} types void and int are inconsistent
 Stop Omega... 0 invocations caught
(Program not linked with -g, cannot print stack backtrace)


*/
