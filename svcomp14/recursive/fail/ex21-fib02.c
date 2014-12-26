extern void __VERIFIER_error() __attribute__ ((__noreturn__));

/*
 * Recursive computation of fibonacci numbers.
 * 
 * Author: Matthias Heizmann
 * Date: 2013-07-13
 * 
 */



int fibonacci(int n)
/*@
  //infer [@post_n]
  requires true
  ensures n<1 & res=0 | n>=1 & res>=0;
 */
{
    if (n < 1) {
        return 0;
    } else if (n == 1) {
        return 1;
    } else {
        return fibonacci(n-1) + fibonacci(n-2);
    }
}

// ex21-fib02.c

extern int __VERIFIER_nondet_int(void)
/*@
  requires true
  ensures true & flow __error;
*/
;

// Expect SUCCESS
// Return FAIL
int main()
/*@
  requires true
  ensures res=0 & flow __norm or true & flow __error;
*/
{
    int x = 9;
    int result = fibonacci(x);
    // dprint;
    if (result == 34) {
      // dprint;
      return 0;
    } else {
      //return 1;
      ERROR: __VERIFIER_error();
    }
}

/*
# svcomp14/recursive/fail/ex10-Fib02-true.c

Why did we report a must-bug. Would this not be
unsound for post-condition proving?

Checking procedure main$... 
Post condition cannot be derived:
  (must) cause:  res=1 |-  res!=1. LOCS:[44;36] (must-bug)

Context of Verification Failure: 1 File "",Line:0,Col:0

Last Proving Location: 1 File "ex10-Fib02-true.c",Line:44,Col:13

ERROR: at _0:0_0:0
Message: Post condition cannot be derived.


 */
