int n,k;

void decrease1(int t)
/*@
  infer [t,n,k]
  requires true
  ensures true;
*/
{
  if (t > 0)
  {
    n--;
    decrease2(t-1);
  }
}

void decrease2(int t)
/*@
  infer [t,n,k]
  requires true
  ensures true;
*/
{
  if (t > 0)
  {
    k--;
    decrease1(t-1);
  }
}

void main()
/*@
  infer [n,k]
  requires true
  ensures true;
*/
{
  n = 10;
  int t=5;
  k = 10;
  decrease1(10);
}
