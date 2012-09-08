//

float abs(float x)
  requires Term[] ensures res = __abs(x);

void foo1a (float x)
  case {
    -0.2 <= x <= 0.1        -> requires Term[] ensures true;
    x > 0.1 | x < -0.2  -> requires Term[Seq{__abs(x)@(0, +infty), 0.1}] ensures true;
  }
{
  if ((x > 0.1) || (x < -0.2))
    foo1a(x / -2.0);
}  

void foo1b (float x)
  case {
    -0.2 <= x <= 0.1  ->  requires Term[] ensures true;
    x > 0.1        ->  requires Term[Seq{x@(0, +infty), (x > 0.1) | (x < -0.2)}] ensures true;
    x < -0.2       ->  requires Term[Seq{-x@(0, +infty), (x > 0.1) | (x < -0.2)}] ensures true;
  }
{
  if ((x > 0.1) || (x < -0.2))
    foo1b(x / -2.0);
}  

