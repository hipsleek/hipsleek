int dec (int x) {
  return x - 1;
}

void loop (int x)
{
  if (x < 0) return;
  else {
    x = dec(x);
    loop(x);
  }
}
