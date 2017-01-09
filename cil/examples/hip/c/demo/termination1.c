int sum1 (int n)
/*@
  case
  {
    n <= 0 -> requires Term[]   ensures true;
    n >  0 -> requires Term[n]  ensures true;
  }
 */
{
  if (n > 0)
    return sum1(n-1)+1;
  else
    return 1;
}
