int fact(int n)
  requires true
  ensures res>0;
{
  int y=1;
  int z=0;
  while (z!=n)
  case {
    z>n -> requires Loop 
           ensures false;
    z<=n -> requires y>0 & z>=0 & Term[n-z] 
            ensures z'=n & y'>0; 
   }
    {
      z=z+1;
      y=y*z;
    }
  return y;
}

