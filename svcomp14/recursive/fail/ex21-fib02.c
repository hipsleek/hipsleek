//extern void __VERIFIER_error() __attribute__ ((__noreturn__));
/*
  requires true
  ensures true & flow __Error;
*/

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
;

// Expect SUCCESS
// Return FAIL
int main()
/*@
  requires true
  ensures res=0 & flow __norm or res=1 & flow __norm; // __Error;
*/
{
    int x = 9;
    int result = fibonacci(x);
    // dprint;
    if (result == 34) {
      // dprint;
      return 0;
    } else {
      return 1;
      //ERROR: __VERIFIER_error();
    }
}

/*
# svcomp14/recursive/fail/ex21-Fib02.c

Are we able to parse external proc of C properly?

globals.ml:let nondet_int_proc_name = "__VERIFIER_nondet_int"
Binary file hip matches
iast.ml:  [ Globals.nondet_int_proc_name; "__VERIFIER_error" ]
parser.ml:(* int __VERIFIER_nondet_int() *)
parser.ml:(* int __VERIFIER_error()      *)
parser.ml:    else if String.compare id "__VERIFIER_error" == 0 then Some (
parser.ml:      "int __VERIFIER_error()\n" ^


*/
