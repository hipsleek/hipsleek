float loop(float x)
  requires Term[SeqCon(x, (1.0 + sqrt(5.0))/2.0, 1.7, 2.0)] ensures true;
{
  if (x < 1.7)
    return x;
  else
    return loop(1.0 + 1.0/x);
}    
