
int buyer(int price, int budget)
  requires  true
{ requires price <= budget
    ensures  res=1;
    requires price > budget
    ensures  res=2;
}
{
  int x = 0;
  dprint;
  if(price <= budget) {
    return 1;
  } else {
    return 2;
  }
}
