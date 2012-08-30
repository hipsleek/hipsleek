/* sqrt examples */

float sqrt1(float x)
  requires x > 0 & Term[]
  ensures res = sqrt(x);

float div2(float x)
  requires true & Term[]
  ensures res = x / 2;
{
  return x / 2;
}  
  
void foo (float x)
  case
  {
    x <= 1  -> requires Term[] ensures true;
    x > 1   -> requires Term[Seq{x, 1.0, 1.1}] ensures true;
  }
{
  if (x > 1.1)
  {
    //float f = div2(x); 
    float f = sqrt1(x);
    foo(f);
  }
  else
    return;
}

