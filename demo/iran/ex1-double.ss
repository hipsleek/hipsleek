int double(int n)
  requires true
  ensures res=2*n & res>=0;
{
  if (n==0) return 0;
  else return 2+double(n-1);
}
