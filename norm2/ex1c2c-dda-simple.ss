data cell { int val; }

void dec (cell x) {
  x.val = x.val - 1;
}

void loop (cell x)
{
  if (x.val < 0) return;
  else {
    dec(x);
    loop(x);
  }
}
