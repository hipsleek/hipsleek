int sum(int n ) 
/*@
  case
  {
    n <= 0 ->  requires true  ensures res = 1;
    n >  0 ->  requires true  ensures res = n+1;
  }
*/
{ 
  int s = 0;
  int i = 0;
  do
  /*@
    case
    {
      i >= n ->  ensures s' = s+1 & i'=i+1;
      i <  n ->  ensures s' = s+(n-i) & i'=n;
    }
  */
  {
    s = s + 1;
    i = i + 1;
  } while (i < n);
  return s;
}
