extern void __VERIFIER_error() __attribute__ ((__noreturn__));

/*
 * Implementation the McCarthy 91 function.
 * http://en.wikipedia.org/wiki/McCarthy_91_function
 * 
 * Author: Matthias Heizmann
 * Date: 2013-07-13
 * 
 */

extern int __VERIFIER_nondet_int(void);


int f91(int x)
/*@
  infer [@post_n]
  requires true
  ensures true;
 */
{
    if (x > 100)
        return x -10;
    else {
        return f91(f91(x+11));
    }
}

// Expect FAIL
// Return FAIL

int main()
/*@
  requires true
  ensures res!=1;
*/
{
    int x = __VERIFIER_nondet_int();
    int result = f91(x);
    if (result == 91 || x > 102 && result == x - 10) {
        return 0;
    } else {
      return 1;
      //ERROR: __VERIFIER_error();
    }
}
