void inc(ref int x) 
requires true
ensures x'=x+1;
{
 x=x+1;
}
int fn()
requires true
ensures res=5;
{ int i;
  i=3;
  inc(i);
  inc(i);
  return i;
}
