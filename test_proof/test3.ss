void foo(ref int x, ref int y)
  requires x>2 & y>=0
  ensures x'=x & y'>1;
{
        x=inc(x);
        y=inc(y);
         x=x-1; 
         y=inc(y);
}

int inc(int x)
 requires x>=0
 ensures res=x+1;
