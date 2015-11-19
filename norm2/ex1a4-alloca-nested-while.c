//#include <stdlib.h>

//extern int __VERIFIER_nondet_int(void);

// ../hip ex1a-alloca-while.c -infer "@shape_prepost@term"

void loop (int* y)
/*@
  infer[@shape_prepost,@term]
  requires true
  ensures true;
*/
{
    while (*y > 0) 
  /*@
    infer[@shape_prepost,@term]
    requires true
    ensures true;
   */
   {
      *y = *y - 1;
    }
}


/*
# ex1a4.ss (FIXED)

# Why do we have split components problem here..
 Why was post-shape scheduled so late?

Context of Verification Failure: _0:0_0:0

Last Proving Location: ex1a4-alloca-nested-while.c_14:4_22:5

ERROR: at _0:0_0:0
Message: split_components: don't expect OR

ExceptionFailure("split_components: don't expect OR")Occurred!

Error1(s) detected at main 
Stop z3... 113 invocations 
Stop Omega... 133 invocations caught

Exception occurred: Failure("split_components: don't expect OR")
Error3(s) detected at main 

*/
