extern int __VERIFIER_nondet_int();
extern void __VERIFIER_error();

/*@
relation fib1(int n, int r).
relation fib2(int n, int r).
*/


int fibo1(int n) 
/*@
infer [fib1,fib2]
requires true
ensures fib1(n,res)
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

int fibo2(int n) 
/*@
infer [fib1,fib2]
requires true
ensures fib2(n,res)
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

int main() 
/*@
 requires true
  ensures true;
*/
{
    int x = 3;
    int result = fibo1(x);
    if (result == 1) {
        __VERIFIER_error();
    }
    return 0;
}
