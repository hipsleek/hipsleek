void loop (int x, int m)
  infer [@term]
  requires true
  ensures true;
{
  if (x != m) {
    if (x > m) x = 0;
    else x = x + 1;
    loop(x, m);
  }
}
