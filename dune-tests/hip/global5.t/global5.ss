
global int n,k;

void increase(int@R k)
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
