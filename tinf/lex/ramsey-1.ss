void loop (int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x != 0) {
    if (x > 0)
      x = x - 1;
    else x = x + 1;
    loop(x);
  }
}
