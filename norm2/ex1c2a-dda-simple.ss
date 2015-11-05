void dec (ref int x) {
  x = x - 1;
}

void loop (int x)
{
  if (x < 0) return;
  else {
    dec(x);
    loop(x);
  }
}
