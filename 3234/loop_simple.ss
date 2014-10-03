int main(int n)
  requires true
  ensures res=n;
{
  int z; //=0;
  while (z!=n)
     requires true
     ensures z'=n; //'
    {
      z=z+1;
    }
  return z;
}

