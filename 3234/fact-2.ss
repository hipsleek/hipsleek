int fact(int n)
  requires n>=0
  ensures res>0;
{
  int y=1;
  int z=0;
  while (z!=n)
     requires y>0 & z>=0 & z<=n & Term[n-z]
     ensures z'=n & y'>0; //'
    {
      z=z+1;
      y=y*z;
    }
  return y;
}

