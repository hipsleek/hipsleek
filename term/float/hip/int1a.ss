/*
float loop(float x)
  case {
    x >= 0.0 -> requires Loop ensures true;
    x < 0.0  -> requires Term[Seq{x, -infty, x < 0.0 -100.0}] ensures true;
  }  
  
{
  if (x < (0.0 - 100.0))
    return x;
  else
    return loop(x * 2.0);
}
*/


int loop(int x)
  case {
    x >= 0 -> requires Loop ensures true;
    x < 0  -> requires Term[x] ensures true;
  }  
{
  if (x < -100)
    return x;
  else
    return loop(x * 2);
}

/*
int loop(int x)
  requires Term[x] ensures true;
{
  if (x < -100)
    return x;
  else
    return loop(x - 2);
}
*/
