extern void __VERIFIER_error() __attribute__ ((__noreturn__));

/*
 * Recursive implementation of the greatest common denominator
 * using Euclid's algorithm
 * 
 * Author: Jan Leike
 * Date: 2013-07-17
 * 
 */

extern int __VERIFIER_nondet_int(void);

// Compute the greatest common denominator using Euclid's algorithm
int gcd(int y1, int y2)
/*@
  infer [@post_n]
  requires true
  ensures true;
 */
{
    if (y1 <= 0 || y2 <= 0) {
        return 0;
    }
    if (y1 == y2) {
        return y1;
    }
    if (y1 > y2) {
        return gcd(y1 - y2, y2);
    }
    return gcd(y1, y2 - y1);
}

// Expect SUCCESS
// Return FAIL

int main()
/*@
  requires true
  ensures res!=1;
*/
{
    int m = __VERIFIER_nondet_int();
    if (m <= 0 || m > 2147483647) {
        return 0;
    }
    int n = __VERIFIER_nondet_int();
    if (n <= 0 || n > 2147483647) {
        return 0;
    }
    int z = gcd(m, n);
    if (z < 1 && m > 0 && n > 0) {
      return 1;
      //ERROR: __VERIFIER_error();
    } else {
        return 0;
    }
}
