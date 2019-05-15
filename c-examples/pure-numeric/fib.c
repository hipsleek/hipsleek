

int fib(int n)
/*@
  infer [@post_n]
  requires true
  ensures true;
*/
{
  if (n <= 1) {
    return n;
  }
  else {
    return fib(n-1) + fib(n-2);
  }
}
