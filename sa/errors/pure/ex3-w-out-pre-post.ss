

relation P(int a).
relation Q(int a, int b).

int foo(int x)
  infer [P,Q] requires P(x) ensures Q(x,res);
{
  if (x<10){
    x=x+1;
    int tmp = foo(x);
    return tmp;
  }

  return x;
}
