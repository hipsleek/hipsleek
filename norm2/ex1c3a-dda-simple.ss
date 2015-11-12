data cell { int val; }

void dec (cell x) 
/*
  infer [@post_n]
  requires true
  ensures true;
*/
{
  x.val = x.val - 1;
}

void loop (int x)
{
  if (x < 0) return;
  else {
    cell y = new cell(x);
    dec(y);
    loop(y.val);
  }
}
