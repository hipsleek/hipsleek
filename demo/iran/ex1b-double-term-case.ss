int double(int n)
 case {
    n>=0 -> 
      requires Term[n]
      ensures res=2*n & res>=0;
    n<0  -> 
      requires Loop
      ensures false;
  }
{
  if (n==0) return 0;
  else return 2+double(n-1);
}
