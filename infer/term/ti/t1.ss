// LOOPS in Transition Invariant paper

void loop2(int y, int x)
  requires y>=1
  case {
   y>=x -> requires Term[] ensures true;
   y<x -> requires Term[x-y] ensures true;
  }
{
  if (y<x) {
    y = 2*y;
    loop2(y,x);
  }
}

void loop1(ref int x)
  //requires x>=-1
  case {
   x<0 -> requires Term[] ensures x'=x; //'
   x>=0 -> requires Term[x+1] ensures x'=-1;//'
  }
{
  if (x>=0) {
    int y=1;
    loop2(y,x);
    x=x-1;
    loop1(x);
  }
}
