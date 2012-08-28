/* div examples */

int div2(int x)
  requires x > 0 & Term[]
  ensures res = x / 2;
{
  return x/2;  
}

void foo (int x)
  case
  {
    x <= 0  -> requires Term[] ensures true;
    x > 0   -> requires Term[x] ensures true;  
  }
{
  if (x > 1)
  {
    int f = div2(x); 
    //int f = x/2;
    foo(f);
    //foo(sqrt1(x));
  }
  else
    return;
}

