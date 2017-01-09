extern void __VERIFIER_error() __attribute__ ((__noreturn__));

/*
 * Recursive computation of fibonacci numbers.
 * 
 * Author: Matthias Heizmann
 * Date: 2013-07-13
 * 
 */

extern int __VERIFIER_nondet_int(void);

/*@
relation fiba(int n, int f).

  //axiom n=0 ==> fiba(n,1).
  //axiom n=1 ==> fiba(n,1).
axiom n<=0 ==> fiba(n,0).
axiom 1<=n<=2 ==> fiba(n,1).ls bugs
axiom n>=2 & fiba(n-1,f1) & fiba(n-2,f2) ==> fiba(n,f1+f2).
//axiom n>2 & fiba(n-1,f1) & fiba(n-2,f2) ==> fiba(n,f1+f2).
*/

int fibonacci(int n)
/*@
  //infer [@post_n]
  requires true
  ensures fiba(n,res);
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

// Expect SUCCESS
// Return FAIL

int main()
/*@
  requires true
  ensures res!=1;
*/
{
    int x = 9;
    int result = fibonacci(x);
    if (result == 34) {
        return 0;
    } else {
      return 1;
      //ERROR: __VERIFIER_error();
    }
}

/*
# svcomp14/recursive/fail/ex10a-Fib02-true.c


Why fiba still fail? Do we need under-approx results?

 */
