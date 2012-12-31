
global int n,k;

void increase(ref int k)
   requires k > 0
   ensures k' = n;
{
   k = n;
   decrease();
}

void decrease()
   requires true
   ensures k' = k-1;
{
   k--;
}