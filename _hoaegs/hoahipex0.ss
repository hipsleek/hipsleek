/**
 Generic testing!
 **/

relation succ(int x, int y) == y = x + 1.

void f(ref int x)
requires true
ensures succ(x,x');
{
  x = x + 1;
}

void g(ref int x)
requires true
ensures x' = x + 5;
{
  x = x + 3;
  f(x);
  f(x);
}
