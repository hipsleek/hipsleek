//

float abs(float x)
  requires Term[] ensures res = __abs(x);

void foo1a (float x)
  case {
    x < 0.1  -> requires Term[] ensures true;
    x >= 0.1 -> requires Term[Seq{__abs(x), (0, +infty), 0.1}] ensures true;
  }
{
  if ((x!=0) && ((x > 0.1) || (x < -0.1)))
    foo1a(x / -2.0);
}  

