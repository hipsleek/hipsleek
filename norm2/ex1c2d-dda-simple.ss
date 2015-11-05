data cell { int val; }

int dec (int x) {
  return x - 1;
}

void loop (cell x)
{
  if (x.val < 0) return;
  else {
    x.val = dec(x.val);
    loop(x);
  }
}
