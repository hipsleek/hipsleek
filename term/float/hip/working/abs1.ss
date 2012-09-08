//

float abs(float x)
  requires Term[] ensures res = __abs(x);

void foo1a (float x)
  case {
    x > -0.2   -> requires Term[] ensures true;
    x <= -0.2  -> requires Term[Seq{-x@(0, +infty), 0.2}] ensures true;
  }
{
  if (x < -0.2)
    foo1a(abs(x) / -2.0);
}  

void foo1b (float x)
  case {
    x > -0.2   -> requires Term[] ensures true;
    x <= -0.2  -> requires Term[Seq{-x@(0, +infty), 0.2}] ensures true;
  }
{
  if (x < -0.2)
    foo1b(abs(x) / -2.0);
}  

