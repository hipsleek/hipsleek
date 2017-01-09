int foo() 
 requires Term
 ensures res >= 0;
 
void loop(int a, int b)
  infer [@term]
  requires true
  ensures true;
  /*
  case {
    b <= 0 -> requires Term[0] ensures true;
    b > 0 -> case {
      a <= 1 -> requires Term[1] ensures true;
      a > 1 -> requires true ensures true;
    }
  }
  */
{
  if (b > 0) {
    int r = foo();
    a = a - 1 - r;
    b = a - 1 - r;
    loop(a, b);
  }
}
