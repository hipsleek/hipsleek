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
axiom 1<=n<=2 ==> fiba(n,1).
axiom n>=2 & fiba(n-1,f1) & fiba(n-2,f2) ==> fiba(n,f1+f2).
*/

int fibonacci(int n) 
/*@
  //infer [@post_n] requires true ensures true;
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
    int x = __VERIFIER_nondet_int();
    if (x > 46) {
        return 0;
    }
    int result = fibonacci(x);
    if (x < 9 || result >= 34) {
        return 0;
    } else {
      return 1;
      //ERROR: __VERIFIER_error();
    }
}
    
/*
# ex11-Fib03-true.c -tp z3

This currently fails. Can under-approx of fixpoint
help somehow? But what kind of query should we give?
Probably need to write some proof obligation for 
these scenarios to determine if problem is at
  (i) imply
  (ii) unsat or sat checking

*/
