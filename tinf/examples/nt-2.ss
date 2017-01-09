void loop (int i, int even)
  infer [@term]
  requires true
  ensures true;
{
  if (i < 0) return;
  else if (even == 0) 
    loop(i+1, 1-even);
  else 
    loop(i-1, 1-even);
}
