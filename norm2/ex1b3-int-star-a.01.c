int test_fun(int* x, int* y)
{
    int c = 0;
    while (*x > 0) {
        *y = 0;
        while (*y < *x) {
            *y = *y + 1;
            c = c + 1;
        }
        *x = *x - 1;
    }
    return c;
}
