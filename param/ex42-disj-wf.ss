void loop (int x, int y)
{
  if (x>0 && y>0) {
    if (__VERIFIER_nondet_int() > 0) 
      loop(x-1, x);
    else 
      loop(y-2, x+1);
  } else return;
}
