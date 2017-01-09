extern int __VERIFIER_nondet_int(void);

int test_fun(int x)
{
  if ( __VERIFIER_nondet_int())
    return (test_fun(x+1));
 else
   return (test_fun(x+2));
}

int main() {
  int x;
    return test_fun(x);
}
