int xZero0(int x, int y)
  requires y=-1 & x=1
  ensures res=0;
{
  if (y<0){//11
    x=0; //12
    dprint;
  }
  return x;
}
