/*
  BUG: current HIP program cannot check termination of a while loop (non recursive program)
*/

float foo (float x)
  case
  {
    x > 0.0 -> requires Term[SeqConDec(x, 1.0, 10.0)] ensures true;
    x <= 0  -> requires Term[] ensures true;
  }
{
  while (x > 10.0)
    x = x / 2.0;
  return x;
}
