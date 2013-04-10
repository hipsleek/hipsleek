int sum(int n)
/*@
  case
  {
    n <= 0 ->  requires true  ensures res = 0;
    n >  0 ->  requires true  ensures res > 0;
  }
*/
{
  int s = 0;
  for (int i = 0; i < n; i++)
    /*@
      case
      {
        i >= n ->  ensures s' = s & i'=i;
        i <  n ->  ensures s' = s+(n-i) & i'=n;
      }
    */
    s = s + 1;
  return s;
}
