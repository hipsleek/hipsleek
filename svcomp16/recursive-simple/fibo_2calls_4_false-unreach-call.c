extern int __VERIFIER_nondet_int();
extern void __VERIFIER_error();

int fibo1(int n);
int fibo2(int n);

int fibo_a(int n) {
    if (n < 1) {
        return 0;
    } else if (n == 1) {
        return 1;
    } else {
        return fibo_b(n-1) + fibo_b(n-2);
    }
}

int fibo_b(int n) {
    if (n < 1) {
        return 0;
    } else if (n == 1) {
        return 1;
    } else {
        return fibo_a(n-1) + fibo_a(n-2);
    }
}

// fibo 1-30
// 1, 1, 2, 3, 5,
// 8, 13, 21, 34, 55, 
// 89, 144, 233, 377, 610,
// 987, 1597, 2584, 4181, 6765,
// 10946, 17711, 28657, 46368, 75025,
// 121393, 196418, 317811, 514229, 832040

int main(void) {
    int x = 4;
    int result = fibo_a(x);
    if (result == 3) {
        ERROR: __VERIFIER_error();
    }
    return 0;
}
