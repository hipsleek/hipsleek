void foo(ref int x, ref int y)
  requires x>2 & y>=0
  ensures x'=x & y'>1;
{
        x=x+1;
        x=x-1;
        y=y+1;
        y=y+1;
}
