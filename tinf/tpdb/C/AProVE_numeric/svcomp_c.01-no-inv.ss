void loop (int x, int y)
{
  if (x <= y) return;
  else {
    loop(x, 2*y);
  }
}

void loop2 (int x, int y)
{
  while (x > y) {
    y = 2*y;
  }
}
