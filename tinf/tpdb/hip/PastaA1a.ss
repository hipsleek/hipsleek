void loop(ref int x, ref int y)
  infer [@post_n]
  requires true
  ensures true;
{
  if (x > y) return;
  else {
    y = y - 1;
    loop(x, y);
  }
}
