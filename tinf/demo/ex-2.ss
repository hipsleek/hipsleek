void loop (int x, int y)
{
  if (x < 0) return;
  else loop(x + y, y);
}

void main ()
{
  int x;
  //loop(x, 0);
  loop(x, -1);
}
