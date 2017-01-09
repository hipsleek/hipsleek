int sum(int n)
/*@
  case
  {
    n <= 0 ->  requires true  ensures res = 0;
    n >  0 ->  requires true  ensures res = n;
  }
*/
{
  int iii;
  iii = 1;
  if (n <= 0)
    return 0;
  else
    return sum(n-1) + 1;
}
