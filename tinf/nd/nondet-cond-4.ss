void loop(int x)
  requires x>=0
  ensures true;
{
  if (x >= 0) {
    x = x + 1;
    loop(x);
  }
}

