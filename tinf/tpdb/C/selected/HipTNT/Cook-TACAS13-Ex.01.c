extern int __VERIFIER_nondet_int();

int main()
{
  int x = __VERIFIER_nondet_int();
  int m = __VERIFIER_nondet_int();
  while (x != m) {
    if (x > m) x = 0;
    else x = x + 1;
  }
  return 0;
}
