int maxfn(int x, int mm)
  requires true
  ensures res=max(x,mm);
{
  if (x>mm) return x;
  else return mm;
}
