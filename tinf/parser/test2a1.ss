/*class ret_int extends __Exc{
  int val
} //exception when return from a loop
*/

int  test_int(int a)
requires true
 ensures a>1 & res=a | a<=1 & res=2;
{
  while (a>1) 
    requires true
    ensures  eres::ret_int<a> & a>1 & flow __RET or a<=1 & flow __norm;
  {
    return a;
  }
  return 2;
  dprint;
}

/*

# test2a.ss

ret_int and ret_bool should be subtypes of __RET
I think there is also a __Return

I think we should just have __RET (and eliminate __Return)
and then have 
  ret_int <: __RET
  ret_int <: __RET

class ret_int extends __Ret { int val }
class ret_bool extends __Ret { bool val } 

For every method, except for while-method; we should
provide:
   try {
     body
   } catch (__RET e)
     e.val
   }


int  test_int(int a)
 requires true
 ensures a>1 & res=a | a<=1 & res=2;
{
 try {
    while_loop(a);
    return 2;
  } catch (__RET e) {
    e.val
  }
}

[(__false,__Fail,(1,2));(__Fail,__flow,(1,3));(__norm,__MayError,(4,5));(__DivByZeroErr,__Error,(6,7));(__ArrBoundErr,__Error,(8,9));(__Error,__MayError,(6,10));(__MayError,__flow,(4,11));(__abort,__flow,(12,13));(__Spec,__others,(14,15));(__Brk_top,__others,(16,17));(__Cont_top,__others,(18,19));(__RET,__others,(20,21));(__Return,__others,(22,23));(__others,__abnormal,(14,24));(ret_int,__Exc,(25,26));(ret_bool,__Exc,(27,28));(__Exc,__abnormal,(25,29));(__abnormal,__cflow,(14,30));(__cflow,__flow,(14,31));(__flow,,(1,32))]

*/
