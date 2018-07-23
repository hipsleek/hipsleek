int fact1_safe(int n)
  requires n <? @Lo
  ensures res <? @Lo;
{
  if(n == 0) {
    return 1;
  } else {
    return n * fact1_safe(n-1);
  }
}
