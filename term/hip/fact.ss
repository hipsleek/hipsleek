

int fact1(int n)
 case {
  n<0 -> requires Loop ensures false;
  n=0 -> requires Term[] ensures res=1;
  n>0 -> requires Term[n-1] ensures res>=1;
}
{
  if (n==0) return 1;
  else return n*fact1(n-1);
}
