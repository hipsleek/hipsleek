int fact(int n)
  requires n<0
  ensures false;
{
  int y=1;
  int z=0;
  while (z!=n)
     requires z>n & Loop
     ensures false; //'
    {
      z=z+1;
      y=y*z;
    }
  return y;
}

