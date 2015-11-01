data cell { int val; }

void dec (ref int x) {
  x = x - 1;
}

void loop (cell x)
{
  if (x.val < 0) return;
  else {
    dec(x.val);
    loop(x);
  }
}
