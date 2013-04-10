int sum(int n ) 
/*@
  case
  {
    n <= 0 ->  requires true  ensures res = 0;
    n >  0 ->  requires true  ensures res = n;
  }
*/
{ 
  int s = 0;
  int i = 0;
  while (i < n)
  /*@
    case
    {
      i >= n ->  ensures s' = s & i'=i;
      i <  n ->  ensures s' = s+(n-i) & i'=n;
    }
  */
  {
    s = s + 1;
    i = i + 1;
  }
  return s;
}
