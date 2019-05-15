int sumn(int n)
/*@
  infer [@post_n]
  requires true
  ensures true;
*/
{
  if (n == 0) {
    return 0;
  }
  else
  {
    return n + sumn(n-1);
  }

}
