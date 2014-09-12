int fact(int x)
 case {
  x>=0 -> ensures res>=1;
}
{
  if (x==0) return 1;
  else return 1 + fact(x - 1);
}
/*
# fact-case.ss

*/
