float loop(float x)
  case {
    x > 1.0 & x < 3.0 -> requires  Term[SeqCon(x, (1.0 + sqrt(5.0))/2.0, x > 1.0)] ensures true;
    x <= 1.0 -> requires true ensures true;
    x >= 3.0 -> requires true ensures true;
  }
{
  if (x < 1.7)
    return x;
  else
    return loop(1.0 + 1.0/x);
}    
