extern int __VERIFIER_nondet_int();
extern void __VERIFIER_error();

void __error()
/*@
  requires emp & true
  ensures emp & true & flow __Error;
*/;


/*@
relation P1(int x).
relation Q1(int x, int y).
 */

int fibo1(int n)
/*@
infer [P1,Q1]
  requires P1(n) ensures Q1(n,res);
 */
 {
    if (n < 1) {
        return 0;
    } else if (n == 1) {
        return 1;
    } else {
        return fibo2(n-1) + fibo2(n-2);
    }
}

/*@
relation P2(int x).
relation Q2(int x, int y).
 */

int fibo2(int n)
/*@
infer [P2,Q2]
  requires P2(n) ensures Q2(n,res);
 */
 {
    if (n < 1) {
        return 0;
    } else if (n == 1) {
        return 1;
    } else {
        return fibo1(n-1) + fibo1(n-2);
    }
}

// fibo 1-30
// 1, 1, 2, 3, 5,
// 8, 13, 21, 34, 55, 
// 89, 144, 233, 377, 610,
// 987, 1597, 2584, 4181, 6765,
// 10946, 17711, 28657, 46368, 75025,
// 121393, 196418, 317811, 514229, 832040

int main() {
    int x = 10;
    int result = fibo1(x);
    if (result != 55) {
        __VERIFIER_error();
    }
    return 0;
}
