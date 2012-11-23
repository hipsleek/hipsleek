int main(int n)
  requires n>=0
  ensures res=n;
{
  int z=0;
  while (z!=n)
     requires z<=n
     ensures z'=n; //'
    {
      z=z+1;
    }
  return z;
}
