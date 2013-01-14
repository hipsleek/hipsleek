void foo(ref int x)
  requires x>=0
  ensures x'=1 or x'>1;
{
  x=x+1;
}

